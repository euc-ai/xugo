// field_model.go — the curve y² = x³ + ax + b inside its function field:
// x and y in a field L with x transcendental over the subfield k, chart 0
// the ring k[x] + k[x]·y, chart 1 the ring k[s] + k[s]·u with s = 1/x
// and u = y/x², glued along A₀[1/x]. The fraction field of the
// Weierstrass ring is such a field; in every such field each quotient of
// a free algebra is isomorphic to its chart, the charts are free of rank
// two over k[x] and k[s], the datum is a curve over the projective line,
// and its structure pair is O(0) · 1 ⊕ O(−2) · y on the line, so the
// genus is one.

package elliptic_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"

	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line_free_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// WeierstrassChartZeroDef — `weierstrass_chart_zero(R, k, x, y)`: the ring
// k[x] + k[x]·y inside the field, the members p + q·y with p and q values
// at x of polynomials over k.
var WeierstrassChartZeroDef = weierstrassChartZeroDefThm{family.Define(registry.DefEntry{
	Name:     "WeierstrassChartZeroDef",
	Key:      "prop_7c3b1a3c0c2850f2",
	Const:    "weierstrass_chart_zero",
	Type:     "ring_ops(A) → set(A) → A → A → set(A)",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀x:A. ∀y:A. " +
			"    weierstrass_chart_zero(R, k, x, y) = " +
			"    {R.add(p, R.mul(q, y)) | " +
			"        p:A, " +
			"        q:A | " +
			"        p ∈ polynomial_image(R, k, x) ∧ q ∈ polynomial_image(R, k, x)}",
	},
	Reading: "The coordinate ring of the affine chart of the curve, read " +
		"inside its function field: a ring once y² lies in k[x], and free over " +
		"k[x] on 1 and y once y lies outside k(x) (WeierstrassBasisZero).",
})}

// WeierstrassChartOneDef — `weierstrass_chart_one(F, k, x, y)`: the ring
// k[s] + k[s]·u inside the field, s = 1/x and u = y/x², the chart at the
// origin.
var WeierstrassChartOneDef = weierstrassChartOneDefThm{family.Define(registry.DefEntry{
	Name:     "WeierstrassChartOneDef",
	Key:      "prop_6d8870e8c285586e",
	Const:    "weierstrass_chart_one",
	Type:     "field_ops(A) → set(A) → A → A → set(A)",
	Implicit: []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. " +
			"    weierstrass_chart_one(F, k, x, y) = " +
			"    {F.add(p, F.mul(q, F.mul(y, F.mul(F.inv(x), F.inv(x))))) | " +
			"        p:A, " +
			"        q:A | " +
			"        p ∈ polynomial_image(field_ring(F), k, F.inv(x)) ∧ " +
			"        q ∈ polynomial_image(field_ring(F), k, F.inv(x))}",
	},
	Reading: "The coordinate ring of the chart at the point at infinity, " +
		"in the coordinates s = 1/x and u = y/x², where the relation reads u² = " +
		"s + as³ + bs⁴ (WeierstrassChartOneEquation). The two charts meet where " +
		"x ≠ 0, and the origin s = u = 0 is the one point of chart 1 off chart 0.",
})}

// WeierstrassDef — `weierstrass(L, k, x, y, a, b)`: k is a subfield of
// L holding a and b, x and y are members of L with y² = x³ + ax + b, x is
// transcendental over k, and L is the field of fractions of chart 0.
var WeierstrassDef = weierstrassDefThm{family.Define(registry.DefEntry{
	Name:     "WeierstrassDef",
	Key:      "prop_8ae9a9d1b235081e",
	Const:    "weierstrass",
	Type:     "field_ops(A) → set(A) → A → A → A → A → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀a:A. ∀b:A. " +
			"    weierstrass(F, k, x, y, a, b) ⇔ " +
			"    subfield(F, k) ∧ " +
			"    a ∈ k ∧ " +
			"    b ∈ k ∧ " +
			"    x ∈ F.carrier ∧ " +
			"    y ∈ F.carrier ∧ " +
			"    F.mul(y, y) = F.add(F.add(F.mul(x, F.mul(x, x)), F.mul(a, x)), b) ∧ " +
			"    ¬algebraic_over(F, k, x) ∧ " +
			"    (∀z:A. " +
			"        z ∈ F.carrier ⇒ " +
			"        ∃p q:A. " +
			"            p ∈ weierstrass_chart_zero(field_ring(F), k, x, y) ∧ " +
			"            q ∈ weierstrass_chart_zero(field_ring(F), k, x, y) ∧ " +
			"            q ≠ F.zero ∧ " +
			"            F.mul(z, q) = p)",
	},
	Reading: "The Weierstrass cubic inside its function field L = k(x, y). Transcendence is " +
		"what the charts' bases and the global sections read: it makes k[x] a polynomial ring and " +
		"keeps y outside k(x) (ChartZeroCoefficientsVanish). No characteristic and no discriminant " +
		"is asked: the nodal and cuspidal cubics are such data too, and the statements that need 2 " +
		"≠ 0 or 4a³ + 27b² ≠ 0 state them, the two together as the smooth datum " +
		"smooth_weierstrass. x is nonzero, zero being algebraic over k (WeierstrassXInvertible).",
	Deps: []registry.EntryLike{WeierstrassChartZeroDef},
})}

// SmoothWeierstrassDef — `smooth_weierstrass(L, k, x, y, a, b)`: a
// Weierstrass datum over a field where 2 ≠ 0 whose discriminant
// 4a³ + 27b² is not zero.
var SmoothWeierstrassDef = smoothWeierstrassDefThm{family.Define(registry.DefEntry{
	Name:     "SmoothWeierstrassDef",
	Key:      "prop_7aa858d21612f2a1",
	Const:    "smooth_weierstrass",
	Type:     "field_ops(A) → set(A) → A → A → A → A → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x y a b:A. " +
			"    smooth_weierstrass(F, k, x, y, a, b) ⇔ " +
			"    weierstrass(F, k, x, y, a, b) ∧ " +
			"    F.add(F.one, F.one) ≠ F.zero ∧ " +
			"    F.add(F.mul(monoid_pow(F.add, F.zero, F.one, 4), F.mul(a, F.mul(a, a))), " +
			"        F.mul(monoid_pow(F.add, F.zero, F.one, 27), F.mul(b, b))) ≠ " +
			"    F.zero",
	},
	Reading: "The two clauses beyond the datum make the cubic smooth: 2 ≠ 0 and 4a³ + 27b² ≠ 0, " +
		"the resultant of x³ + ax + b and its derivative, are what WeierstrassChartPartialsUnit reads to " +
		"make the Jacobian pair span each chart. finite(k) is no part of it: finiteness is a property of " +
		"the field of constants, and the statements that count points state it beside the datum.",
	Deps: []registry.EntryLike{WeierstrassDef},
})}

// SmoothWeierstrassDatum — a smooth Weierstrass datum is a Weierstrass datum.
var SmoothWeierstrassDatum = smoothWeierstrassDatumThm{family.Add(registry.ProofEntry{
	Name:  "SmoothWeierstrassDatum",
	Key:   "prop_ac6dcf8a8e9e8006",
	Build: SmoothWeierstrassDef.Entry().Conjunct("weierstrass(F, k, x, y, a, b)"),
})}

// ---------------------------------------------------------------------------
// The datum read conjunct by conjunct, x a unit, and the members of the charts
// ---------------------------------------------------------------------------

// WeierstrassSubfield — the constants k of a datum are a subfield of L.
var WeierstrassSubfield = weierstrassSubfieldThm{family.Add(registry.ProofEntry{
	Name:  "WeierstrassSubfield",
	Key:   "prop_8920b1abca4809af",
	Build: WeierstrassDef.Entry().Conjunct("subfield(F, k)"),
})}

// WeierstrassCoefficientA — the coefficient a of a datum lies in k.
var WeierstrassCoefficientA = weierstrassCoefficientAThm{family.Add(registry.ProofEntry{
	Name:  "WeierstrassCoefficientA",
	Key:   "prop_4b979da972f1b763",
	Build: WeierstrassDef.Entry().Conjunct("a ∈ k"),
})}

// WeierstrassCoefficientB — the coefficient b of a datum lies in k.
var WeierstrassCoefficientB = weierstrassCoefficientBThm{family.Add(registry.ProofEntry{
	Name:  "WeierstrassCoefficientB",
	Key:   "prop_d3acb9cb6ea73f07",
	Build: WeierstrassDef.Entry().Conjunct("b ∈ k"),
})}

// WeierstrassXInField — the coordinate x of a datum lies in L.
var WeierstrassXInField = weierstrassXInFieldThm{family.Add(registry.ProofEntry{
	Name:  "WeierstrassXInField",
	Key:   "prop_5c883a49f2202a03",
	Build: WeierstrassDef.Entry().Conjunct("x ∈ F.carrier"),
})}

// WeierstrassYInField — the coordinate y of a datum lies in L.
var WeierstrassYInField = weierstrassYInFieldThm{family.Add(registry.ProofEntry{
	Name:  "WeierstrassYInField",
	Key:   "prop_6cb219d93da15a1",
	Build: WeierstrassDef.Entry().Conjunct("y ∈ F.carrier"),
})}

// WeierstrassEquation — the coordinates of a datum satisfy the cubic:
// y² = x³ + ax + b.
var WeierstrassEquation = weierstrassEquationThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassEquation",
	Key:  "prop_931a5f1811741fa0",
	Build: WeierstrassDef.Entry().Conjunct(
		"F.mul(y, y) = F.add(F.add(F.mul(x, F.mul(x, x)), F.mul(a, x)), b)"),
})}

// WeierstrassTranscendental — the coordinate x of a datum is
// transcendental over k.
var WeierstrassTranscendental = weierstrassTranscendentalThm{family.Add(registry.ProofEntry{
	Name:  "WeierstrassTranscendental",
	Key:   "prop_bcb53973772ceb08",
	Build: WeierstrassDef.Entry().Conjunct("¬algebraic_over(F, k, x)"),
})}

// WeierstrassFractionField — L is the field of fractions of chart 0: each
// member of L is a quotient p/q of members of chart 0.
var WeierstrassFractionField = weierstrassFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassFractionField",
	Key:  "prop_47b0de6467c04987",
	Build: WeierstrassDef.Entry().Conjunct(Statement{
		Binders: "∀z:A.",
		Hypotheses: []string{
			"z ∈ F.carrier",
		},
		Conclusion: "∃p q:A. " +
			"    p ∈ weierstrass_chart_zero(field_ring(F), k, x, y) ∧ " +
			"    q ∈ weierstrass_chart_zero(field_ring(F), k, x, y) ∧ " +
			"    q ≠ F.zero ∧ " +
			"    F.mul(z, q) = p",
	}),
})}

// WeierstrassXInvertible — the coordinate x of a datum is a unit of L:
// zero is algebraic over k and x is not, so x ≠ zero, and inv(x) inverts
// it on either side.
var WeierstrassXInvertible = weierstrassXInvertibleThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassXInvertible",
	Key:  "prop_bb449fed1fa3807",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "x ≠ L.zero ∧ L.inv(x) ∈ L.carrier ∧ x * L.inv(x) = L.one ∧ L.inv(x) * x = L.one",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			xm := arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact())
			nonzero := arg.Have(
				"x is not zero, being transcendental over k",
				"x ≠ L.zero",
				By(
					WeierstrassSubfield.Read(datum),
					WeierstrassTranscendental.Read(datum),
					algebraic_element.TranscendentalInverse.Read(L).At(k, xm)))
			arg.Show(
				"so inv(x) lies in L and inverts x on either side",
				By(
					nonzero,
					field.InvIn.Read(L).At(xm),
					field.MulRightInverseOn.Read(L).At(xm),
					field.MulLeftInverseOn.Read(L).At(xm)))
		}),
})}

// WeierstrassChartZeroMembers — a member of chart 0 is p + q·y with p and
// q in k[x], and every such sum is one: the definition read pointwise.
var WeierstrassChartZeroMembers = weierstrassChartZeroMembersThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartZeroMembers",
	Key:  "prop_2f50d960ec52928e",
	Build: family.Theorem("∀R:ring_ops(A). ∀k:set(A). ∀x y z:A. "+
		"    z ∈ weierstrass_chart_zero(R, k, x, y) ⇔ "+
		"    ∃p q:A. "+
		"        p ∈ polynomial_image(R, k, x) ∧ q ∈ polynomial_image(R, k, x) ∧ z = R.add(p, R.mul(q, y))",
		func(arg *Argument, R *Expr[RingOps[A]], k *Expr[Set[A]], x, y, z *Expr[A]) {
			arg.Show(
				"the members of chart 0 are its defining sums",
				Unfold(WeierstrassChartZeroDef),
				SetTac())
		}),
})}

// WeierstrassChartOneMembers — a member of chart 1 is p + q·u with p and
// q in k[s], s = inv(x) and u = y · inv(x)², and every such sum is one:
// the definition read pointwise.
var WeierstrassChartOneMembers = weierstrassChartOneMembersThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartOneMembers",
	Key:  "prop_2952b1d1d119b4f3",
	Build: family.Theorem("∀F:field_ops(A). ∀k:set(A). ∀x y z:A. "+
		"    z ∈ weierstrass_chart_one(F, k, x, y) ⇔ "+
		"    ∃p q:A. "+
		"        p ∈ polynomial_image(field_ring(F), k, F.inv(x)) ∧ "+
		"        q ∈ polynomial_image(field_ring(F), k, F.inv(x)) ∧ "+
		"        z = F.add(p, F.mul(q, F.mul(y, F.mul(F.inv(x), F.inv(x)))))",
		func(arg *Argument, F *Expr[field.FieldOps[A]], k *Expr[Set[A]], x, y, z *Expr[A]) {
			arg.Show(
				"the members of chart 1 are its defining sums",
				Unfold(WeierstrassChartOneDef),
				SetTac())
		}),
})}

// ---------------------------------------------------------------------------
// The curve inside its function field
// ---------------------------------------------------------------------------

// ChartZeroCoefficientsVanish — one and y are independent over k[x]: a
// combination p + q·y with p and q in k[x] vanishes only when p and q do.
// Write p = P(x) and q = Q(x) for polynomials P and Q over k, and C for
// the cubic x³ + ax + b over k, of degree three. Then p² = q²·y² =
// q²·C(x), so P·P = Q·Q·C as polynomials, x being transcendental over k.
// Were Q nonzero, so would be Q·Q·C and with it P, and the degrees would
// make 2·deg P three more than 2·deg Q, an even number three more than an
// even number; so Q is the zero polynomial, q = Q(x) = zero, and p = −q·y
// is zero.
var ChartZeroCoefficientsVanish = chartZeroCoefficientsVanishThm{family.Add(registry.ProofEntry{
	Name: "ChartZeroCoefficientsVanish",
	Key:  "prop_ffacaa03f9e5cef4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b p q:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"p ∈ polynomial_image(field_ring(L), k, x)",
			"q ∈ polynomial_image(field_ring(L), k, x)",
			"p + q * y = L.zero",
		},
		Conclusion: "p = L.zero ∧ q = L.zero",
		Abbrev: Abbrev{
			{Name: "weierstrassCubicPolynomial", Text: "vec_add( " +
				"    vec_add(basis_vector(3), vec_scalar_mul(a, basis_vector(1))), " +
				"    vec_scalar_mul(b, basis_vector(0)))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b, p, q *Expr[A], h Fact) {
			given := arg.Conjuncts(
				h,
				"the Weierstrass datum",
				"p lies in k[x]",
				"so does q",
				"and p + q·y is zero")
			datum, pIn, qIn, vanishes := given[0], given[1], given[2], given[3]
			subK, aInK, bInK :=
				WeierstrassSubfield.Read(datum).AsFact(),
				WeierstrassCoefficientA.Read(datum),
				WeierstrassCoefficientB.Read(datum)
			xInL, yInL := WeierstrassXInField.Read(datum).AsFact(), WeierstrassYInField.Read(datum).AsFact()
			relation, transcendental :=
				WeierstrassEquation.Read(datum).AsFact(), WeierstrassTranscendental.Read(datum)
			ring := field.RingOn.Read(L)
			xm := arg.MemberOf[on.L](x, xInL)
			zero, three := arg.TermAs[A]("L.zero"), arg.TermAs[Nat]("3")
			kInL := arg.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			fieldK := arg.Have(
				"k is a field in its own right",
				"field_on(restrict_field(L, k))",
				By(subK, field.SubfieldFieldOn.Read(L).At(k)))
			ringK := field.RingOn.Read(fieldK)
			domainK := integral_domain.FieldIntegralDomain.Read(fieldK)
			polynomialsK := polynomial.PolynomialRingOn.Read(ringK)

			// p and q are the values at x of polynomials P and Q over k.
			inImage := arg.Have(
				"k[x] is the set of the values at x of the polynomials over k",
				"∀z:A. "+
					"    z ∈ polynomial_image(field_ring(L), k, x) ⇔ "+
					"    ∃P:(num → A). polynomial_over(k, P) ∧ z = polynomial_eval(P, x)",
				Unfold(algebraic_element.PolynomialImageDef),
				SetTac())
			imageSubring := arg.Have(
				"k[x] is a subring of L",
				"subring(field_ring(L), polynomial_image(field_ring(L), k, x))",
				By(subK, xInL, algebraic_element.PolynomialImageRing.Read(L).At(k, xm)))
			members := arg.Have(
				"p and q lie in L, as k[x] does, and a and b, as k does",
				"p ∈ L.carrier ∧ q ∈ L.carrier ∧ a ∈ L.carrier ∧ b ∈ L.carrier",
				BySets(comm_ring.SubringSubset.Read(imageSubring), pIn, qIn, kInL, aInK, bInK))
			P, pPolynomial := arg.ObtainAs[Fun[Nat, A]](
				"p is the value at x of a polynomial P over k",
				"∃P:(num → A). polynomial_over(k, P) ∧ p = polynomial_eval(P, x)",
				By(inImage.At(p), pIn))
			Q, qPolynomial := arg.ObtainAs[Fun[Nat, A]](
				"and q the value at x of a polynomial Q over k",
				"∃Q:(num → A). polynomial_over(k, Q) ∧ q = polynomial_eval(Q, x)",
				By(inImage.At(q), qIn))
			pFacts := arg.Conjuncts(
				pPolynomial,
				"P is a polynomial over k",
				"whose value at x is p")
			qFacts := arg.Conjuncts(
				qPolynomial,
				"Q is a polynomial over k",
				"whose value at x is q")
			pOver, pValue, qOver, qValue := pFacts[0], pFacts[1], qFacts[0], qFacts[1]
			squares := arg.Have(
				"p = −q·y, so p² = q²·y² = q²·(x³ + ax + b)",
				"p * p = (q * q) * (x * (x * x) + a * x + b)",
				ByArith(
					ring,
					Scaled(arg.TermAs[A]("p - q * y"), vanishes),
					Scaled(arg.TermAs[A]("q * q"), relation),
					xInL,
					yInL,
					members))

			// The cubic C = x³ + ax + b over k: its value at x, its leading coefficient and its degree.
			C, cubicDefined := arg.LetAs[Fun[Nat, A]]("C", "«weierstrassCubicPolynomial»")
			cOver := arg.Have(
				"C is a polynomial over k, a and b lying in k",
				"polynomial_over(k, C)",
				cubicDefined.Rw(),
				BySets(
					aInK,
					bInK,
					polynomial.BasisVectorOver.Read(ringK),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ringK)),
					comm_ring.AddIn.Read(polynomialsK)))
			termsOverL := arg.Have(
				"the terms of C and their sums are polynomials over L",
				"polynomial_over(L.carrier, basis_vector(3)) ∧ "+
					"polynomial_over(L.carrier, basis_vector(1)) ∧ "+
					"polynomial_over(L.carrier, basis_vector(0)) ∧ "+
					"polynomial_over(L.carrier, vec_scalar_mul(a, basis_vector(1))) ∧ "+
					"polynomial_over(L.carrier, vec_scalar_mul(b, basis_vector(0))) ∧ "+
					"polynomial_over(L.carrier, vec_add(basis_vector(3), vec_scalar_mul(a, basis_vector(1))))",
				BySets(
					members,
					polynomial.BasisVectorOver.Read(ring),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
					comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ring))))
			cValue := arg.Have(
				"C takes the value x³ + ax + b at x",
				"polynomial_eval(C, x) = x * (x * x) + a * x + b",
				cubicDefined.Rw(),
				Simp(
					Fwd(polynomial_evaluation.EvalAdd.Read(ring)),
					Fwd(polynomial_evaluation.EvalScalar.Read(ring)),
					Fwd(polynomial_evaluation.EvalBasisVector.Read(ring)),
					Fwd(termsOverL)),
				ByArith(ring, xInL, members))
			cLeading := arg.Have(
				"its coefficient at 3 is one",
				"C(3) = L.one",
				cubicDefined.Rw(),
				Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
				ByArith(ring, members))
			cPast := arg.Have(
				"and C vanishes past 3",
				"vec⟨suc(3)⟩(C)",
				cubicDefined.Rw(),
				Simp(
					Fwd(vec_space.VecDef),
					Fwd(vec_space.VecAddDef),
					Fwd(vec_space.VecScalarMulDef),
					Fwd(vec_space.BasisVectorDef)),
				Derive(func(c *Argument) {
					c.FixAs[Nat]("i")
					c.Show(
						"past 3 every term of C is zero",
						ByArith(ring, c.Assume(), members))
				}))
			oneNotZero := field.OneNotZeroOn.Read(L)
			cDegree := arg.Have(
				"so C has degree 3, being one at 3",
				"polynomial_degree(C) = 3",
				By(cPast, cLeading, oneNotZero, polynomial.DegreeExact.Read(cOver).At(three)))
			cNonzero := arg.Have(
				"and C is not the zero polynomial, being one at 3",
				"C ≠ vec_zero",
				By(Normalized, cLeading, vec_space.VecZeroDef.At(zero, three), oneNotZero))

			// P·P = Q·Q·C as polynomials over k, their values agreeing at the transcendental x.
			squareP := arg.TermAs[Fun[Nat, A]]("polynomial_mul(P, P)")
			squareQ := arg.TermAs[Fun[Nat, A]]("polynomial_mul(Q, Q)")
			right := arg.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_mul(Q, Q), C)")
			productsOver := arg.Have(
				"Q·Q, P·P and Q·Q·C are polynomials over k",
				"polynomial_over(k, polynomial_mul(Q, Q)) ∧ "+
					"polynomial_over(k, polynomial_mul(P, P)) ∧ "+
					"polynomial_over(k, polynomial_mul(polynomial_mul(Q, Q), C))",
				By(pOver, qOver, cOver, polynomial.PolynomialMulOver.Read(ringK)))
			factorsOverL := arg.Have(
				"P, Q, C and Q·Q are polynomials over L as well",
				"polynomial_over(L.carrier, P) ∧ "+
					"polynomial_over(L.carrier, Q) ∧ "+
					"polynomial_over(L.carrier, C) ∧ "+
					"polynomial_over(L.carrier, polynomial_mul(Q, Q))",
				By(kInL, pOver, qOver, cOver, productsOver, polynomial.PolynomialOverMono))
			values := arg.Have(
				"evaluation at x multiplies: P·P takes the value p², Q·Q·C the value q²·(x³ + ax + b)",
				"polynomial_eval(polynomial_mul(P, P), x) = p * p ∧ "+
					"polynomial_eval(polynomial_mul(polynomial_mul(Q, Q), C), x) = (q * q) * (x * (x * x) + a * x + b)",
				Simp(Fwd(polynomial_evaluation.EvalMul.Read(ring)), Fwd(factorsOverL)),
				By(Normalized, pValue, qValue, cValue))
			identity := arg.Have(
				"so P·P = Q·Q·C, x being transcendental over k",
				"polynomial_mul(P, P) = polynomial_mul(polynomial_mul(Q, Q), C)",
				By(
					subK,
					xInL,
					transcendental,
					productsOver,
					values,
					squares,
					algebraic_element.EvalInjectiveTranscendental.Read(L).At(k, xm, squareP, right)))

			// Q is the zero polynomial: otherwise the degrees of the two sides differ in parity.
			parity := arg.Have(
				"no even number is three more than another",
				"∀m n:num. m + m ≠ n + n + 3",
				Derive(func(c *Argument) {
					m := c.FixAs[Nat]("m")
					c.FixAs[Nat]("n")
					equal := c.SupposeNot()
					forms := c.Have(
						"m + m would be both 2·m and the successor of 2·(n + 1)",
						"2 * m = m + m ∧ suc(2 * (n + 1)) = m + m",
						ByArith(equal))
					c.Show(
						"and so even and odd at once",
						By(
							forms,
							nat_parity.EvenDouble.At(m),
							nat_parity.OddSucDouble.At(c.TermAs[Nat]("n + 1")),
							nat_parity.NotEvenAndOdd.At(c.TermAs[Nat]("m + m"))))
				}))
			qZeroPolynomial := arg.Have(
				"Q is the zero polynomial",
				"Q = vec_zero",
				Derive(func(c *Argument) {
					qNonzero := c.SupposeNot()
					qm := proof.MemberOf(Q, c.Have(
						"Q lies in the ring of the polynomials over k",
						"Q ∈ {f:(num → A) | polynomial_over(k, f)}",
						BySets(qOver)))
					squareQm := proof.MemberOf(squareQ, c.Have(
						"and so does Q·Q",
						"polynomial_mul(Q, Q) ∈ {f:(num → A) | polynomial_over(k, f)}",
						BySets(productsOver)))
					cm := proof.MemberOf(C, c.Have(
						"and C",
						"C ∈ {f:(num → A) | polynomial_over(k, f)}",
						BySets(cOver)))
					pm := proof.MemberOf(P, c.Have(
						"and P",
						"P ∈ {f:(num → A) | polynomial_over(k, f)}",
						BySets(pOver)))
					noZeroDivisors := integral_domain.NoZeroDivisors.Read(polynomial.PolynomialDomain.Read(domainK))
					squareNonzero := c.Have(
						"the polynomials over the field k form a domain, so Q·Q is not zero",
						"polynomial_mul(Q, Q) ≠ vec_zero",
						By(qNonzero, noZeroDivisors.At(qm, qm)))
					rightNonzero := c.Have(
						"nor is Q·Q·C",
						"polynomial_mul(polynomial_mul(Q, Q), C) ≠ vec_zero",
						By(squareNonzero, cNonzero, noZeroDivisors.At(squareQm, cm)))
					pNonzero := c.Have(
						"so P is not zero, zero times zero being zero",
						"P ≠ vec_zero",
						By(identity, rightNonzero, comm_ring.MulLeftZeroOn.Read(polynomialsK).At(pm)))
					pDegree := c.Have(
						"P·P has degree 2·deg P",
						"polynomial_degree(polynomial_mul(P, P)) = polynomial_degree(P) + polynomial_degree(P)",
						By(pNonzero, pOver, polynomial.DegreeMul.Read(domainK).At(P, P)))
					qDegree := c.Have(
						"Q·Q has degree 2·deg Q",
						"polynomial_degree(polynomial_mul(Q, Q)) = polynomial_degree(Q) + polynomial_degree(Q)",
						By(qNonzero, qOver, polynomial.DegreeMul.Read(domainK).At(Q, Q)))
					rightDegree := c.Have(
						"and Q·Q·C the degree of Q·Q plus that of C",
						"polynomial_degree(polynomial_mul(polynomial_mul(Q, Q), C)) = "+
							"polynomial_degree(polynomial_mul(Q, Q)) + polynomial_degree(C)",
						By(squareNonzero, cNonzero, productsOver, cOver, polynomial.DegreeMul.Read(domainK).At(squareQ, C)))
					sameDegree := c.Have(
						"the two sides being one polynomial, Q·Q·C has degree 2·deg P",
						"polynomial_degree(polynomial_mul(polynomial_mul(Q, Q), C)) = "+
							"polynomial_degree(P) + polynomial_degree(P)",
						By(identity, pDegree))
					c.Show(
						"so 2·deg P = 2·deg Q + 3, an even number three more than an even number",
						ByArith(
							parity.At(c.TermAs[Nat]("polynomial_degree(P)"), c.TermAs[Nat]("polynomial_degree(Q)")),
							sameDegree,
							rightDegree,
							qDegree,
							cDegree))
				}))

			// So q = Q(x) is zero, and then p = −q·y is.
			qZero := arg.Have(
				"so q, the value of Q, is zero",
				"q = L.zero",
				By(Normalized, qValue, qZeroPolynomial, polynomial_evaluation.EvalVecZero.Read(ring).At(xm)))
			arg.Show(
				"and p = −q·y is zero",
				ByArith(ring, Scaled(y, qZero), vanishes, yInL, members))
		}),
})}

// WeierstrassBasisZero — chart 0 is a subring of the field containing
// k[x], free over k[x] on 1 and y: it is k[x] + k[x]·y, with y² =
// x³ + ax + b in k[x], so a ring (fractional_ideal.RingOneAndElement);
// and 1 and y are independent over k[x] (ChartZeroCoefficientsVanish), so
// a basis (fractional_ideal.BasisOneAndElement).
var WeierstrassBasisZero = weierstrassBasisZeroThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassBasisZero",
	Key:  "prop_6b3cfc412b31665d",
	Reading: "A product of two members is (p + qy)(p' + q'y) = (pp' + qq'(x³ + ax + " +
		"b)) + (pq' + qp')y, so chart 0 is a ring because a and b lie in k. The basis " +
		"reads the transcendence of x: for x algebraic over k, k[x] is the field k(x), and " +
		"1 and y need not be independent over it. one ≠ y says the basis has two members.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "subring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)) ∧ " +
			"polynomial_image(field_ring(L), k, x) ⊆ weierstrass_chart_zero(field_ring(L), k, x, y) ∧ " +
			"module_basis(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, x)), " +
			"    restrict_module(regular_module(field_ring(L)), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"    {L.one, y}) ∧ " +
			"¬(L.one = y)",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			// k is a subfield of L: the line of x is read under it.
			kSubfield := arg.Simplified(WeierstrassSubfield.Read(datum).AsFact())
			aInK, bInK, relation :=
				WeierstrassCoefficientA.Read(datum),
				WeierstrassCoefficientB.Read(datum),
				WeierstrassEquation.Read(datum).AsFact()
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			polynomials := arg.Conjuncts(
				GroupPremises(kSubfield, algebraic_element.PolynomialImageRing.Read(L).At(k, xm)),
				"k[x] is a subring of L",
				"holding k",
				"and x",
				"inside k(x)")
			subringX, kInKx, xInKx := polynomials[0], polynomials[1], polynomials[2]

			// y² = x³ + ax + b lies in k[x].
			coefficients := arg.Have(
				"a and b lie in k[x], as k does",
				"a ∈ «curveKx» ∧ b ∈ «curveKx»",
				BySets(kInKx, aInK, bInK))
			square := arg.Have(
				"y² = x³ + ax + b lies in k[x], as x, a and b do",
				"y * y ∈ «curveKx»",
				relation.Rw(),
				By(xInKx, coefficients, comm_ring.SubringAdd.Read(subringX), comm_ring.SubringMul.Read(subringX)))

			// 1 and y are independent over k[x].
			independence := arg.Have(
				"c + d·y = zero with c and d in k[x] has c = d = zero",
				"∀c d:A. c ∈ «curveKx» ∧ d ∈ «curveKx» ∧ c + d * y = L.zero ⇒ c = L.zero ∧ d = L.zero",
				By(datum, ChartZeroCoefficientsVanish.Read(L).AsFact().At(k, x, y, a, b)))

			kxT := arg.TermAs[Set[A]]("«curveKx»")
			arg.Show(
				"chart 0 is k[x] + k[x]·y: a ring inside L holding k[x], free over k[x] on one and y",
				Unfold(WeierstrassChartZeroDef),
				By(
					subringX,
					square,
					independence,
					fractional_ideal.RingOneAndElement.Read(L).At(kxT, ym),
					fractional_ideal.BasisOneAndElement.Read(L).At(kxT, ym)))
		}),
})}

// WeierstrassChartOneEquation — u² = s(1 + as² + bs³) in the field: the
// Weierstrass relation divided by x⁴, the relation of chart 1 and, with
// s and u vanishing there, the relation at the origin. x, transcendental,
// is not zero, so x · s = one: the relation times s⁴ is the equation.
var WeierstrassChartOneEquation = weierstrassChartOneEquationThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartOneEquation",
	Key:  "prop_93dee797a0e01be8",
	Reading: "u² = y²/x⁴ = (x³ + ax + b)/x⁴ = s + as³ + bs⁴: the " +
		"Weierstrass relation divided by x⁴, which x ≠ zero allows.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "y * (L.inv(x) * L.inv(x)) * (y * (L.inv(x) * L.inv(x))) = " +
			"L.inv(x) * (L.one + a * (L.inv(x) * L.inv(x)) + b * (L.inv(x) * (L.inv(x) * L.inv(x))))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], h Fact) {
			relation := arg.Simplified(WeierstrassEquation.Read(h).AsFact())
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(h).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(h).AsFact())
			sm := field.InvIn.Read(L).At(xm)
			ring := field.RingOn.Read(L)

			coefficients := arg.Have(
				"a and b lie in L, as k does",
				"a ∈ L.carrier ∧ b ∈ L.carrier",
				BySets(
					WeierstrassSubfield.Read(h),
					field.SubfieldSubset,
					WeierstrassCoefficientA.Read(h),
					WeierstrassCoefficientB.Read(h)))
			unit := arg.Conjuncts(
				GroupPremises(h, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")[2]

			arg.Show(
				"u² is the relation times inv(x)⁴, read in powers of x · inv(x)",
				CalcEq(
					Leg(
						arg.TermAs[A]("(x * (x * x) + a * x + b) * (L.inv(x) * L.inv(x) * (L.inv(x) * L.inv(x)))"),
						"u² = y² · inv(x)⁴ = (x³ + ax + b) · inv(x)⁴",
						ByArith(
							ring,
							xm,
							ym,
							sm,
							coefficients,
							Scaled(arg.TermAs[A]("L.inv(x) * L.inv(x) * (L.inv(x) * L.inv(x))"), relation))),
					Leg(
						arg.TermAs[A](
							"x * L.inv(x) * (x * L.inv(x) * (x * L.inv(x))) * L.inv(x) + "+
								"a * (x * L.inv(x)) * (L.inv(x) * (L.inv(x) * L.inv(x))) + "+
								"b * (L.inv(x) * (L.inv(x) * (L.inv(x) * L.inv(x))))"),
						"x³ · inv(x)⁴ = (x · inv(x))³ · inv(x) and x · inv(x)⁴ = (x · inv(x)) · inv(x)³",
						ByArith(ring, xm, sm, coefficients)),
					FinalLeg(
						"and x · inv(x) = one",
						unit.Rw(),
						ByArith(ring, xm, sm, coefficients)),
				))
		}),
})}

// WeierstrassLaurentCoefficients — one and y are independent over the
// Laurent polynomials k[x, 1/x]: c + d · y = zero with c and d in
// k[x, 1/x] has c = d = zero. Powers xᵐ and xⁿ carry c and d into k[x],
// and multiplied by xᵐ · xⁿ the relation is one over k[x], which the
// independence of 1 and y over k[x] (ChartZeroCoefficientsVanish) allows
// only at zero; no power of x being zero, d is zero, and then so is
// c = −d · y.
var WeierstrassLaurentCoefficients = weierstrassLaurentCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassLaurentCoefficients",
	Key:  "prop_bf76c527169a169",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b c d:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"c ∈ ring_away(field_ring(L), polynomial_image(field_ring(L), k, x), x)",
			"d ∈ ring_away(field_ring(L), polynomial_image(field_ring(L), k, x), x)",
			"c + d * y = L.zero",
		},
		Conclusion: "c = L.zero ∧ d = L.zero",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), «curveKx»)"},
			{Name: "p", Text: "monoid_pow(L.mul, L.one, x, n) * (monoid_pow(L.mul, L.one, x, m) * c)"},
			{Name: "q", Text: "monoid_pow(L.mul, L.one, x, m) * (monoid_pow(L.mul, L.one, x, n) * d)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b, c, d *Expr[A], h Fact) {
			given := arg.Conjuncts(
				h,
				"(L, k, x, y, a, b) is a Weierstrass datum",
				"c lies in k[x, 1/x]",
				"so does d",
				"c + d · y = zero")
			ringL := field.RingOn.Read(L)
			powersL := comm_ring.MulMonoidOn.Read(ringL)
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(given[0]).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(given[0]).AsFact())
			sm := field.InvIn.Read(L).At(xm)
			invertible := arg.Conjuncts(
				GroupPremises(given[0], WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")
			unit := invertible[2]

			// The line of x: k[x] is a ring holding x, and the overlap lies in L.
			fieldRing, kxT := arg.TermAs[RingOps[A]]("field_ring(L)"), arg.TermAs[Set[A]]("«curveKx»")
			kSubfield := arg.Simplified(WeierstrassSubfield.Read(given[0]).AsFact())
			line := arg.Simplified(
				GroupPremises(invertible[0], kSubfield, projective_line.LineDatum.Read(L).At(k, xm)))
			ringX := arg.Have(
				"k[x], a subring of L, is a ring under the field's operations",
				"comm_ring_on(«scalars»)",
				By(line, comm_ring.SubringRingOn.Read(ringL).At(kxT)))
			xInKx := arg.Have(
				"x lies in k[x]",
				"x ∈ «curveKx»",
				By(line))
			overlapSubring := arg.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), «curveLaurent»)",
				By(line))
			overlapInL := arg.Have(
				"so it lies in L",
				"«curveLaurent» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(overlapSubring)))
			cm := arg.MemberOf[on.L](c, arg.Have(
				"c lies in L",
				"c ∈ L.carrier",
				BySets(given[1], overlapInL)))
			dm := arg.MemberOf[on.L](d, arg.Have(
				"and so does d",
				"d ∈ L.carrier",
				BySets(given[2], overlapInL)))

			nonzeroPowers := arg.Have(
				"no power of x is zero: xʲ · inv(x)ʲ is one, as x · inv(x) is, and one is not zero",
				"∀j:num. monoid_pow(L.mul, L.one, x, j) ≠ L.zero",
				arg.ForEach(func(j *Expr[Nat]) Action {
					return By(
						unit,
						field.OneNotZeroOn.Read(L),
						comm_monoid.PowInverseOn.Read(powersL).At(xm, sm, j),
						comm_ring.MulLeftZeroOn.Read(ringL).At(comm_monoid.PowIn.Read(powersL).At(sm, j)))
				}))

			// Clearing the denominators: c + d · y = zero becomes p + q · y = zero over k[x].
			const (
				p = "monoid_pow(L.mul, L.one, x, n) * (monoid_pow(L.mul, L.one, x, m) * c)"
				q = "monoid_pow(L.mul, L.one, x, m) * (monoid_pow(L.mul, L.one, x, n) * d)"
			)
			m, cCleared := arg.ObtainAs[Nat](
				"a power xᵐ carries c into k[x]",
				"∃m:num. monoid_pow(L.mul, L.one, x, m) * c ∈ «curveKx»",
				By(given[1], ring_away.RingAwayMember.At(fieldRing, kxT, x, c)))
			n, dCleared := arg.ObtainAs[Nat](
				"and a power xⁿ carries d",
				"∃n:num. monoid_pow(L.mul, L.one, x, n) * d ∈ «curveKx»",
				By(given[2], ring_away.RingAwayMember.At(fieldRing, kxT, x, d)))
			powersX := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringX))
			pIn := arg.Have(
				"p, xⁿ times xᵐ · c, lies in k[x]",
				"«p» ∈ «curveKx»",
				By(comm_ring.MulIn.Read(ringX), powersX, xInKx, cCleared))
			qIn := arg.Have(
				"and so does q, xᵐ times xⁿ · d",
				"«q» ∈ «curveKx»",
				By(comm_ring.MulIn.Read(ringX), powersX, xInKx, dCleared))
			cleared := arg.Have(
				"multiplied by xᵐ · xⁿ, c + d · y = zero is p + q · y = zero",
				"«p» + «q» * y = L.zero",
				ByArith(
					ringL,
					xm,
					ym,
					cm,
					dm,
					Scaled(arg.TermAs[A]("monoid_pow(L.mul, L.one, x, m) * monoid_pow(L.mul, L.one, x, n)"), given[3])))
			both := arg.Conjuncts(
				arg.Have(
					"so p and q are zero, one and y being independent over k[x]",
					"«p» = L.zero ∧ «q» = L.zero",
					By(
						given[0],
						pIn,
						qIn,
						cleared,
						ChartZeroCoefficientsVanish.Read(L).At(k, x, y, a, b, arg.TermAs[A]("«p»"), arg.TermAs[A]("«q»")))),
				"p is zero",
				"q is zero")
			powerM, powerN :=
				comm_monoid.PowIn.Read(powersL).At(xm, m), comm_monoid.PowIn.Read(powersL).At(xm, n)
			dZero := arg.Have(
				"q = xᵐ · (xⁿ · d) is zero and no power of x is, so d is zero",
				"d = L.zero",
				By(
					both[1],
					nonzeroPowers.At(m),
					nonzeroPowers.At(n),
					field.MulEqZeroOn.Read(L).At(powerM, comm_ring.MulIn.Read(ringL).At(powerN, dm)),
					field.MulEqZeroOn.Read(L).At(powerN, dm)))
			cZero := arg.Have(
				"then c = −d · y is zero",
				"c = L.zero",
				ByArith(ringL, cm, dm, ym, given[3], Scaled(y, dZero)))
			arg.Show(
				"both coefficients vanish",
				By(cZero, dZero))
		}),
})}

// WeierstrassBasisOne — chart 1 is a subring of the field containing
// k[s], free over k[s] on 1 and u: it is k[s] + k[s]·u, with u² =
// s · (1 + as² + bs³) in k[s] (WeierstrassChartOneEquation), so a ring
// (fractional_ideal.RingOneAndElement); and c + d·u = zero over k[s] is
// c + (d·s²)·y = zero over k[x, 1/x], where 1 and y are independent
// (WeierstrassLaurentCoefficients), so 1 and u are a basis
// (fractional_ideal.BasisOneAndElement).
var WeierstrassBasisOne = weierstrassBasisOneThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassBasisOne",
	Key:  "prop_6304e1f2c0b78ea6",
	Reading: "Chart 1 is a ring because u² = s(1 + as² + bs³) lies in k[s] " +
		"(WeierstrassChartOneEquation). 1 and u are independent over k[s] as 1 " +
		"and y are over k(x), u being y/x². one ≠ u says the basis has two members.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "subring(field_ring(L), weierstrass_chart_one(L, k, x, y)) ∧ " +
			"polynomial_image(field_ring(L), k, L.inv(x)) ⊆ weierstrass_chart_one(L, k, x, y) ∧ " +
			"module_basis(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(x))), " +
			"    restrict_module(regular_module(field_ring(L)), weierstrass_chart_one(L, k, x, y)), " +
			"    {L.one, y * (L.inv(x) * L.inv(x))}) ∧ " +
			"¬(L.one = y * (L.inv(x) * L.inv(x)))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], h Fact) {
			aInK, bInK := WeierstrassCoefficientA.Read(h), WeierstrassCoefficientB.Read(h)
			ringL := field.RingOn.Read(L)
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(h).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(h).AsFact())
			sm := field.InvIn.Read(L).At(xm)
			um := comm_ring.MulIn.Read(ringL).At(ym, comm_ring.MulIn.Read(ringL).At(sm, sm))
			invertible := arg.Conjuncts(
				GroupPremises(h, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")
			unit := invertible[2]

			// The line of x: k[s], s = inv(x), and the overlap k[x, 1/x] are
			// subrings of L, and k[s] lies in the overlap.
			kSubfield := arg.Simplified(WeierstrassSubfield.Read(h).AsFact())
			line := arg.Simplified(
				GroupPremises(invertible[0], kSubfield, projective_line.LineDatum.Read(L).At(k, xm)))
			subringS := arg.Have(
				"k[s] is a subring of L",
				"subring(field_ring(L), «curveKs»)",
				By(line))
			kInKs := arg.Have(
				"k lies in k[s]",
				"k ⊆ «curveKs»",
				By(line))
			subringOverlap := arg.Have(
				"the overlap k[x, 1/x] is a subring of L",
				"subring(field_ring(L), «curveLaurent»)",
				By(line))
			ksInOverlap := arg.Have(
				"the overlap holds k[s]",
				"«curveKs» ⊆ «curveLaurent»",
				By(line))
			ksInL := arg.Have(
				"k[s] lies in L",
				"«curveKs» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subringS)))

			// u² = s · (one + a · s² + b · s³) lies in k[s].
			inKs := arg.Unfolded(kInKs, set_basic.SubsetDef)
			square := arg.Have(
				"u² lies in k[s]: it is s · (one + a · s² + b · s³), and k[s] holds s, one, a and b",
				"«curveU» * «curveU» ∈ «curveKs»",
				GroupPremises(h, WeierstrassChartOneEquation.Read(L).At(k, x, y, a, b)).Rw(),
				By(
					line,
					inKs.At(a),
					aInK,
					inKs.At(b),
					bInK,
					comm_ring.SubringOne.Read(subringS),
					comm_ring.SubringMul.Read(subringS),
					comm_ring.SubringAdd.Read(subringS)))

			// Chart 1: c + d · u = zero with c and d in k[s] is c + (d · s²) · y = zero over k[x, 1/x].
			inOverlap := arg.Unfolded(ksInOverlap, set_basic.SubsetDef)
			chartOneCoefficients := arg.Have(
				"so c + d · u = zero with c and d in k[s] has c = d = zero",
				"∀c d:A. c ∈ «curveKs» ∧ d ∈ «curveKs» ∧ c + d * «curveU» = L.zero ⇒ c = L.zero ∧ d = L.zero",
				Derive(func(sub *Argument) {
					c, d := sub.FixAs[A]("c"), sub.FixAs[A]("d")
					given := sub.Conjuncts(
						sub.Assume(),
						"c lies in k[s]",
						"so does d",
						"c + d · u = zero")
					cm := sub.MemberOf[on.L](c, sub.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(given[0], ksInL)))
					dm := sub.MemberOf[on.L](d, sub.Have(
						"and so does d",
						"d ∈ L.carrier",
						BySets(given[1], ksInL)))
					dIn := sub.Have(
						"d · s² lies in k[x, 1/x], a product of members of that ring",
						"d * (L.inv(x) * L.inv(x)) ∈ «curveLaurent»",
						By(inOverlap.At(d), given[1], line, comm_ring.SubringMul.Read(subringOverlap)))
					relation := sub.Have(
						"c + d · u is c + (d · s²) · y",
						"c + d * (L.inv(x) * L.inv(x)) * y = L.zero",
						ByArith(ringL, cm, dm, xm, ym, given[2]))
					both := sub.Conjuncts(
						sub.Have(
							"so c and d · s² are zero, one and y being independent over k[x, 1/x]",
							"c = L.zero ∧ d * (L.inv(x) * L.inv(x)) = L.zero",
							By(
								h,
								inOverlap.At(c),
								given[0],
								dIn,
								relation,
								WeierstrassLaurentCoefficients.Read(L).At(
									k, x, y, a, b, c, sub.TermAs[A]("d * (L.inv(x) * L.inv(x))")))),
						"c is zero",
						"d · s² is zero")
					dZero := sub.Have(
						"then d = x² · (d · s²) is zero, x · s being one",
						"d = L.zero",
						ByArith(
							ringL,
							dm,
							xm,
							Scaled(sub.TermAs[A]("x * x"), both[1]),
							Scaled(sub.TermAs[A]("d * (x * L.inv(x) + L.one)"), unit)))
					sub.Show(
						"both coefficients vanish",
						By(both[0], dZero))
				}))

			ksT := arg.TermAs[Set[A]]("«curveKs»")
			arg.Show(
				"chart 1 is k[s] + k[s]·u: a ring inside L holding k[s], free over k[s] on one and u",
				Unfold(WeierstrassChartOneDef),
				By(
					subringS,
					square,
					chartOneCoefficients,
					fractional_ideal.RingOneAndElement.Read(L).At(ksT, um),
					fractional_ideal.BasisOneAndElement.Read(L).At(ksT, um)))
		}),
})}

// ChartZeroAwayInChartOne — for x a nonzero member of the field and y any
// member, a power of 1/x carries every member of k[x] + k[x]·y with x
// inverted into k[1/x] + k[1/x]·y/x²: A₀[1/x] ⊆ A₁[x]. If xⁿ · z = p + q·y
// with p and q in k[x], then z = c₀ + c₁·u with c₀ = inv(x)ⁿ · p and
// c₁ = x² · inv(x)ⁿ · q, both in the line's overlap k[x, 1/x], which is
// k[1/x] with inv(x) inverted (LaurentThroughInverse). So powers
// inv(x)^m₁ and inv(x)^m₂ carry c₀ and c₁ into k[1/x], and
// inv(x)^(m₁ + m₂) carries z into chart 1.
var ChartZeroAwayInChartOne = chartZeroAwayInChartOneThm{family.Add(registry.ProofEntry{
	Name: "ChartZeroAwayInChartOne",
	Key:  "prop_52a6a155ec4ab0cd",
	Reading: "Only x ≠ zero is asked: no relation between x and y and no transcendence. " +
		"Read at the coordinates 1/x and y/x² of chart 1 it is the other inclusion, chart 0 " +
		"there being chart 1 here and chart 1 there chart 0 here (WeierstrassOverlap).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"x ∈ L.carrier",
			"x ≠ L.zero",
			"y ∈ L.carrier",
		},
		Conclusion: "ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x) ⊆ " +
			"ring_away(field_ring(L), weierstrass_chart_one(L, k, x, y), L.inv(x))",
		Abbrev: Abbrev{
			{Name: "second", Text: "x * x * (monoid_pow(L.mul, L.one, L.inv(x), n) * q)"},
			{Name: "first", Text: "monoid_pow(L.mul, L.one, L.inv(x), n) * p"},
			{Name: "firstCleared", Text: "monoid_pow(L.mul, L.one, L.inv(x), m₂) * " +
				"(monoid_pow(L.mul, L.one, L.inv(x), m₁) * («first»))"},
			{Name: "secondCleared", Text: "monoid_pow(L.mul, L.one, L.inv(x), m₁) * " +
				"(monoid_pow(L.mul, L.one, L.inv(x), m₂) * («second»))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"k is a subfield of L",
				"x lies in L",
				"x is not zero",
				"y lies in L")
			subK, xInL, nonzero, yInL := parts[0], parts[1], parts[2], parts[3]
			xm, ym := arg.MemberOf[on.L](x, xInL), arg.MemberOf[on.L](y, yInL)
			ixm := field.InvIn.Read(L).At(xm)
			ring := field.RingOn.Read(L)
			powers := comm_ring.MulMonoidOn.Read(ring)
			fieldOps := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			unit := arg.Have(
				"x · inv(x) = one",
				"x * L.inv(x) = L.one",
				By(nonzero, field.MulRightInverseOn.Read(L).At(xm)))

			// The line at x: its overlap k[x, 1/x] is k[x] with x inverted, and k[1/x] with inv(x) inverted.
			line := arg.Conjuncts(
				arg.Have(
					"on the line at x, k[x] lies in the subring k[x, 1/x] of L, "+
						"which holds inv(x), and k[1/x] is a subring holding inv(x)",
					"«curveKx» ⊆ «curveLaurent» ∧ "+
						"subring(field_ring(L), «curveLaurent») ∧ "+
						"subring(field_ring(L), «curveKs») ∧ "+
						"x ∈ «curveKx» ∧ "+
						"L.inv(x) ∈ «curveKs» ∧ "+
						"L.inv(x) ∈ «curveLaurent»",
					By(subK, xInL, nonzero, projective_line.LineDatum.Read(L).At(k, xm))),
				"k[x] lies in k[x, 1/x]",
				"k[x, 1/x] is a subring of L",
				"k[1/x] is a subring of L",
				"x lies in k[x]",
				"inv(x) lies in k[1/x]",
				"inv(x) lies in k[x, 1/x]")
			laurentT, inverseT := arg.TermAs[Set[A]]("«curveLaurent»"), arg.TermAs[Set[A]]("«curveKs»")
			laurentRing := arg.Have(
				"k[x, 1/x] is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «curveLaurent»))",
				By(line[1], comm_ring.SubringRingOn.Read(ring).At(laurentT)))
			inverseRing := arg.Have(
				"so is k[1/x]",
				"comm_ring_on(restrict_ring(field_ring(L), «curveKs»))",
				By(line[2], comm_ring.SubringRingOn.Read(ring).At(inverseT)))
			laurentInL := arg.Have(
				"k[x, 1/x] lies in L",
				"«curveLaurent» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(line[1])))
			throughInverse := arg.Have(
				"k[x, 1/x] is also k[1/x] with inv(x) inverted",
				"ring_away(field_ring(L), «curveKs», L.inv(x)) = «curveLaurent»",
				By(subK, xInL, nonzero, projective_line.LaurentThroughInverse.Read(L).At(k, xm)))
			clears := arg.Have(
				"so a power of inv(x) carries each member of k[x, 1/x] into k[1/x]",
				"∀f:A. "+
					"    f ∈ «curveLaurent» ⇔ "+
					"    f ∈ L.carrier ∧ (∃m:num. monoid_pow(L.mul, L.one, L.inv(x), m) * f ∈ «curveKs»)",
				Simp(Rev(throughInverse), Fwd(ring_away.RingAwayMember)),
				Basic())

			arg.Show(
				"A₀[1/x] ⊆ A₁[x], member by member",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(sub *Argument) {
					const (
						first  = "monoid_pow(L.mul, L.one, L.inv(x), n) * p"
						second = "x * x * (monoid_pow(L.mul, L.one, L.inv(x), n) * q)"
					)
					z := sub.FixAs[A]("z")
					zIn := sub.Assume()
					opened := sub.Conjuncts(
						sub.Have(
							"z lies in L, and a power of x carries it into chart 0",
							"z ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, x, n) * z ∈ «curveChart0»)",
							By(zIn, ring_away.RingAwayMember.At(fieldOps, sub.TermAs[Set[A]]("«curveChart0»"), x, z))),
						"z lies in L",
						"a power of x carries z into chart 0")
					zm := sub.MemberOf[on.L](z, opened[0])
					n, cleared := sub.UnpackAs[Nat](opened[1], "n")
					p, q, split := sub.Obtain2As[A, A](
						"so xⁿ · z = p + q · y with p and q in k[x]",
						"∃p q:A. p ∈ «curveKx» ∧ q ∈ «curveKx» ∧ monoid_pow(L.mul, L.one, x, n) * z = p + q * y",
						By(
							cleared,
							WeierstrassChartZeroMembers.At(
								fieldOps, k, x, y, sub.TermAs[A]("monoid_pow(L.mul, L.one, x, n) * z"))))
					coefficients := sub.Conjuncts(
						split,
						"p lies in k[x]",
						"q lies in k[x]",
						"xⁿ · z = p + q · y")
					inLaurent := sub.Have(
						"p, q and x lie in k[x, 1/x], as k[x] does",
						"p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ x ∈ «curveLaurent»",
						BySets(line[0], coefficients[0], coefficients[1], line[3]))
					pm := sub.MemberOf[on.L](p, sub.Have(
						"so p lies in L",
						"p ∈ L.carrier",
						BySets(inLaurent, laurentInL)))
					qm := sub.MemberOf[on.L](q, sub.Have(
						"and so does q",
						"q ∈ L.carrier",
						BySets(inLaurent, laurentInL)))

					// z = c₀ + c₁ · u with c₀ and c₁ in k[x, 1/x]; a power of inv(x) clears each into k[1/x].
					overlapCoefficients := sub.Conjuncts(
						sub.Have(
							"inv(x)ⁿ · p and x² · inv(x)ⁿ · q lie in the ring k[x, 1/x], which holds inv(x)",
							"«first» ∈ «curveLaurent» ∧ «second» ∈ «curveLaurent»",
							By(
								comm_ring.MulIn.Read(laurentRing),
								comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(laurentRing)),
								line[5],
								inLaurent)),
						"inv(x)ⁿ · p lies in k[x, 1/x]",
						"x² · inv(x)ⁿ · q lies in k[x, 1/x]")
					cancel := sub.Have(
						"xⁿ · inv(x)ⁿ = one, as x · inv(x) = one",
						"monoid_pow(L.mul, L.one, x, n) * monoid_pow(L.mul, L.one, L.inv(x), n) = L.one",
						By(unit, comm_monoid.PowInverseOn.Read(powers).At(xm, ixm, n)))
					decomposition := sub.Have(
						"so z = inv(x)ⁿ · (p + q · y) = inv(x)ⁿ · p + (x² · inv(x)ⁿ · q) · u",
						"z = «first» + «second» * («curveU»)",
						ByArith(
							ring,
							zm,
							pm,
							qm,
							xm,
							ym,
							ixm,
							Scaled(sub.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(x), n)"), coefficients[2]),
							Scaled(z, cancel),
							Scaled(
								sub.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(x), n) * q * y * (x * L.inv(x) + L.one)"), unit)))
					m1, firstPower := sub.ObtainAs[Nat](
						"a power inv(x)^m₁ carries inv(x)ⁿ · p into k[1/x]",
						"∃m₁:num. monoid_pow(L.mul, L.one, L.inv(x), m₁) * («first») ∈ «curveKs»",
						By(clears.At(sub.TermAs[A]("«first»")), overlapCoefficients[0]))
					m2, secondPower := sub.ObtainAs[Nat](
						"and a power inv(x)^m₂ carries x² · inv(x)ⁿ · q",
						"∃m₂:num. monoid_pow(L.mul, L.one, L.inv(x), m₂) * («second») ∈ «curveKs»",
						By(clears.At(sub.TermAs[A]("«second»")), overlapCoefficients[1]))

					// inv(x)^(m₁ + m₂) clears both.
					inversePowers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(inverseRing))
					bothCleared := sub.Have(
						"inv(x)^m₂ · inv(x)^m₁ · c₀ and inv(x)^m₁ · inv(x)^m₂ "+
							"· c₁ lie in the ring k[1/x], which holds inv(x)",
						"«firstCleared» ∈ «curveKs» ∧ «secondCleared» ∈ «curveKs»",
						By(comm_ring.MulIn.Read(inverseRing), inversePowers, line[4], firstPower, secondPower))
					exponents := sub.Have(
						"inv(x)^(m₁ + m₂) = inv(x)^m₁ · inv(x)^m₂",
						"monoid_pow(L.mul, L.one, L.inv(x), m₁ + m₂) = "+
							"monoid_pow(L.mul, L.one, L.inv(x), m₁) * monoid_pow(L.mul, L.one, L.inv(x), m₂)",
						By(comm_monoid.PowAddOn.Read(powers).At(ixm, m1, m2)))
					expansion := sub.Have(
						"so inv(x)^(m₁ + m₂) · z is the first cleared coefficient plus the second times u",
						"monoid_pow(L.mul, L.one, L.inv(x), m₁ + m₂) * z = «firstCleared» + «secondCleared» * («curveU»)",
						ByArith(
							ring,
							zm,
							pm,
							qm,
							xm,
							ym,
							ixm,
							Scaled(z, exponents),
							Scaled(
								sub.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(x), m₁) * monoid_pow(L.mul, L.one, L.inv(x), m₂)"),
								decomposition)))
					coefficientsInChart := sub.Have(
						"inv(x)^(m₁ + m₂) · z = P + Q · u with P and Q in k[1/x]",
						"∃P Q:A. "+
							"    P ∈ «curveKs» ∧ "+
							"    Q ∈ «curveKs» ∧ "+
							"    monoid_pow(L.mul, L.one, L.inv(x), m₁ + m₂) * z = P + Q * «curveU»",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[A]("«firstCleared»"))
							c.Take(c.TermAs[A]("«secondCleared»"))
							c.Show(
								"the two cleared coefficients",
								By(expansion, bothCleared))
						}))
					inChartOne := sub.Have(
						"so inv(x)^(m₁ + m₂) carries z into chart 1",
						"monoid_pow(L.mul, L.one, L.inv(x), m₁ + m₂) * z ∈ «curveChart1»",
						By(
							coefficientsInChart,
							WeierstrassChartOneMembers.At(
								sub.TermAs[field.FieldOps[A]]("L"),
								k,
								x,
								y,
								sub.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(x), m₁ + m₂) * z"))))
					sub.Show(
						"so z lies in A₁[x]",
						By(
							opened[0],
							inChartOne,
							ring_away.RingAwayMember.At(
								fieldOps, sub.TermAs[Set[A]]("«curveChart1»"), sub.TermAs[A]("L.inv(x)"), z)))
				}))
		}),
})}

// WeierstrassOverlap — the two charts have one overlap: A₀[1/x] =
// A₁[x] inside the field. Read in the coordinates 1/x and u = y/x² of
// chart 1, chart 0 is chart 1 and chart 1 is chart 0, so both inclusions
// are ChartZeroAwayInChartOne: once at (x, y), and once at (1/x, u),
// where inverting 1/x returns x. Transcendence gives x ≠ zero.
var WeierstrassOverlap = weierstrassOverlapThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassOverlap",
	Key:  "prop_c856cbaf7c5e6358",
	Reading: "The two charts glue along one ring: chart 0 with x inverted is chart 1 with " +
		"1/x inverted. Of the datum only x ≠ zero is read; the equality holds for every y in L.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x) = " +
			"ring_away(field_ring(L), weierstrass_chart_one(L, k, x, y), L.inv(x))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			subK, xInL, yInL :=
				WeierstrassSubfield.Read(datum),
				WeierstrassXInField.Read(datum).AsFact(),
				WeierstrassYInField.Read(datum).AsFact()
			xm, ym := arg.MemberOf[on.L](x, xInL), arg.MemberOf[on.L](y, yInL)
			ring := field.RingOn.Read(L)
			invertible := arg.Conjuncts(
				GroupPremises(datum, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")
			nonzero, unit := invertible[0], invertible[2]
			ixm := arg.MemberOf[on.L](arg.TermAs[A]("L.inv(x)"), invertible[1])
			um := arg.MemberOf[on.L](arg.TermAs[A]("«curveU»"), arg.Have(
				"u = y · inv(x)² lies in L",
				"«curveU» ∈ L.carrier",
				By(comm_ring.MulIn.Read(ring).At(ym, comm_ring.MulIn.Read(ring).At(ixm, ixm)))))

			forward := arg.Have(
				"A₀[1/x] ⊆ A₁[x]: a power of inv(x) carries chart 0 with x inverted into chart 1",
				"ring_away(field_ring(L), «curveChart0», x) ⊆ ring_away(field_ring(L), «curveChart1», L.inv(x))",
				By(subK, xInL, nonzero, yInL, At(Read(ChartZeroAwayInChartOne, L), k, x, y)))

			// Chart 1 read from the coordinates inv(x) and u.
			twice := arg.Have(
				"inverting inv(x) returns x",
				"L.inv(L.inv(x)) = x",
				By(field.InvInvOn.Read(L).At(xm)))
			back := arg.Have(
				"so u · x² = y",
				"«curveU» * (x * x) = y",
				ByArith(ring, xm, ym, ixm, Scaled(arg.TermAs[A]("y * (x * L.inv(x) + L.one)"), unit)))
			chartZeroSwapped := arg.Have(
				"chart 0 at (inv(x), u) is chart 1 at (x, y): both are k[1/x] + k[1/x] · u",
				"weierstrass_chart_zero(field_ring(L), k, L.inv(x), «curveU») = «curveChart1»",
				Simp(Fwd(WeierstrassChartZeroDef), Fwd(WeierstrassChartOneDef)),
				Refl())
			chartOneSwapped := arg.Have(
				"and chart 1 at (inv(x), u) is chart 0 at (x, y): its "+
					"ring is k[inv(inv(x))] = k[x], and u · inv(inv(x))² = y",
				"weierstrass_chart_one(L, k, L.inv(x), «curveU») = «curveChart0»",
				Simp(Fwd(WeierstrassChartOneDef), Fwd(WeierstrassChartZeroDef), Fwd(twice), Fwd(back)),
				Basic())
			swapped := arg.Have(
				"the same inclusion at the coordinates (inv(x), u) of chart 1",
				"ring_away(field_ring(L), "+
					"    weierstrass_chart_zero(field_ring(L), k, L.inv(x), «curveU»), "+
					"    L.inv(x)) ⊆ "+
					"ring_away(field_ring(L), weierstrass_chart_one(L, k, L.inv(x), «curveU»), L.inv(L.inv(x)))",
				By(
					subK,
					ixm,
					nonzero,
					field.InvEqZeroOn.Read(L).At(xm),
					um,
					At(Read(ChartZeroAwayInChartOne, L), k, ixm, um)))
			backward := arg.Simplified(swapped, Fwd(chartZeroSwapped), Fwd(chartOneSwapped), Fwd(twice))
			arg.Show(
				"A₁[x] ⊆ A₀[1/x] as well, so the two sets are one",
				By(forward, backward, set_order.SubsetAntisym))
		}),
})}

// WeierstrassGlobalSections — the functions regular on both charts are
// the constants: A₀ ∩ A₁ = k. A common member is p + q·y with p, q in
// k[x] and P + Q·y/x² with P, Q in k[1/x]; a power of x carries P and
// Q/x² into k[x], and 1, y being independent over k[x]
// (ChartZeroCoefficientsVanish), p = P and q = Q/x². So p and q lie in
// k[x] ∩ k[1/x] = k (LineGlobalSections), and q is zero: otherwise
// x = Q/(x·q) would lie in k[1/x], hence in k, and x is transcendental.
var WeierstrassGlobalSections = weierstrassGlobalSectionsThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassGlobalSections",
	Key:  "prop_cac32e634dc35984",
	Reading: "The point at infinity is what makes the curve complete: the functions " +
		"regular on both charts are the constants, H⁰ = k. Transcendence is load-bearing: " +
		"for x algebraic over k, k[x] and k[1/x] are one field k(x), and the charts share it.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "weierstrass_chart_zero(field_ring(L), k, x, y) ∩ " +
			"weierstrass_chart_one(L, k, x, y) = " +
			"k",
		Abbrev: Abbrev{
			{Name: "weierstrassGlobalSectionsInvXn", Text: "monoid_pow(L.mul, L.one, L.inv(x), n)"},
			{Name: "weierstrassGlobalSectionsInvXm", Text: "monoid_pow(L.mul, L.one, L.inv(x), m)"},
			{Name: "weierstrassGlobalSectionsClearedP0", Text: "(monoid_pow(L.mul, L.one, x, n) * " +
				"    monoid_pow(L.mul, L.one, x, m)) * " +
				"p"},
			{Name: "weierstrassGlobalSectionsClearedQ0", Text: "((monoid_pow(L.mul, L.one, x, n) * " +
				"        monoid_pow(L.mul, L.one, x, m)) * " +
				"    q)"},
			{Name: "weierstrassGlobalSectionsClearedP1", Text: "monoid_pow(L.mul, L.one, x, m) * " +
				"(monoid_pow(L.mul, L.one, x, n) * P)"},
			{Name: "weierstrassGlobalSectionsClearedQ1", Text: "(monoid_pow(L.mul, L.one, x, n) * " +
				"    (monoid_pow(L.mul, L.one, x, m) * (Q * (L.inv(x) * L.inv(x)))))"},
			{Name: "weierstrassGlobalSectionsDifferenceAtOne", Text: "(«weierstrassGlobalSectionsClearedP0» - " +
				"    «weierstrassGlobalSectionsClearedP1»)"},
			{Name: "weierstrassGlobalSectionsDifferenceAtY", Text: "(«weierstrassGlobalSectionsClearedQ0» - " +
				"    «weierstrassGlobalSectionsClearedQ1»)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			subK, transcendental := WeierstrassSubfield.Read(datum), WeierstrassTranscendental.Read(datum)
			xInL, yInL := WeierstrassXInField.Read(datum).AsFact(), WeierstrassYInField.Read(datum).AsFact()
			xm, ym := arg.MemberOf[on.L](x, xInL), arg.MemberOf[on.L](y, yInL)
			ringL := field.RingOn.Read(L)
			powersL := comm_ring.MulMonoidOn.Read(ringL)
			invertible := arg.Conjuncts(
				GroupPremises(datum, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")
			nonzero, unit := invertible[0], invertible[2]
			invXm := field.InvIn.Read(L).At(xm)

			// The line of x: its charts k[x] and k[1/x] and their overlap k[x, 1/x].
			line := arg.Conjuncts(
				arg.Have(
					"k[x] and k[1/x] are subrings of L holding k, x and "+
						"inv(x), inside the overlap k[x, 1/x], a subring of L",
					"k ⊆ «curveKx» ∧ "+
						"k ⊆ «curveKs» ∧ "+
						"«curveKx» ⊆ «curveLaurent» ∧ "+
						"«curveKs» ⊆ «curveLaurent» ∧ "+
						"subring(field_ring(L), «curveLaurent») ∧ "+
						"subring(field_ring(L), «curveKx») ∧ "+
						"subring(field_ring(L), «curveKs») ∧ "+
						"x ∈ «curveKx» ∧ "+
						"L.inv(x) ∈ «curveKs»",
					By(subK, xInL, nonzero, projective_line.LineDatum.Read(L).At(k, xm))),
				"k lies in k[x]",
				"k lies in k[1/x]",
				"k[x] lies in the overlap",
				"k[1/x] lies in the overlap",
				"the overlap is a subring of L",
				"k[x] is a subring of L",
				"k[1/x] is a subring of L",
				"x lies in k[x]",
				"inv(x) lies in k[1/x]")
			kInKx, kInKs, kxInOverlap, ksInOverlap, xInKx, invInKs :=
				line[0], line[1], line[2], line[3], line[7], line[8]
			kx, ks := arg.TermAs[Set[A]]("«curveKx»"), arg.TermAs[Set[A]]("«curveKs»")
			ringKx := arg.Have(
				"k[x] is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «curveKx»))",
				By(line[5], comm_ring.SubringRingOn.Read(ringL).At(kx)))
			ringKs := arg.Have(
				"and so is k[1/x]",
				"comm_ring_on(restrict_ring(field_ring(L), «curveKs»))",
				By(line[6], comm_ring.SubringRingOn.Read(ringL).At(ks)))
			meet := arg.Have(
				"transcendence makes k[x] ∩ k[1/x] = k",
				"«curveKx» ∩ «curveKs» = k",
				By(subK, xInL, transcendental, projective_line.LineGlobalSections.Read(L).At(k, xm)))
			constants := arg.Have(
				"so the members of both k[x] and k[1/x] are the constants",
				"∀v:A. v ∈ «curveKx» ∧ v ∈ «curveKs» ⇔ v ∈ k",
				BySets(meet))
			fieldOps := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			expandZero := WeierstrassChartZeroMembers.Inst[A]().At(fieldOps, k, x, y)
			expandOne := WeierstrassChartOneMembers.Inst[A]().At(arg.TermAs[field.FieldOps[A]]("L"), k, x, y)
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")

			common := arg.Have(
				"a member of both charts is a constant",
				"∀z:A. z ∈ «curveChart0» ∩ «curveChart1» ⇒ z ∈ k",
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					both := c.Assume()
					charts := c.Conjuncts(
						c.Have(
							"z lies in chart 0 and in chart 1",
							"z ∈ «curveChart0» ∧ z ∈ «curveChart1»",
							By(both, set_basic.InInter.At(chart0, chart1, z))),
						"z lies in chart 0",
						"z lies in chart 1")
					_, q, first := c.Obtain2As[A, A](
						"z is p + q·y with p and q in k[x]",
						"∃p q:A. p ∈ «curveKx» ∧ q ∈ «curveKx» ∧ z = p + q * y",
						By(expandZero, charts[0]))
					inChart0 := c.Conjuncts(
						first,
						"p lies in k[x]",
						"q lies in k[x]",
						"z = p + q·y")
					P, _, second := c.Obtain2As[A, A](
						"and z is P + Q·u with P and Q in k[1/x]",
						"∃P Q:A. P ∈ «curveKs» ∧ Q ∈ «curveKs» ∧ z = P + Q * «curveU»",
						By(expandOne, charts[1]))
					inChart1 := c.Conjuncts(
						second,
						"P lies in k[1/x]",
						"Q lies in k[1/x]",
						"z = P + Q·u")

					// Clearing the denominators: xⁿ · P and xᵐ · Q · inv(x)² lie in k[x].
					n, clearedP := c.ObtainAs[Nat](
						"P lies in the overlap, so a power xⁿ carries it into k[x]",
						"∃n:num. monoid_pow(L.mul, L.one, x, n) * P ∈ «curveKx»",
						By(inChart1[0], ksInOverlap, ring_away.RingAwayMember.At(fieldOps, kx, x, P), set_basic.SubsetDef))
					quotient := c.TermAs[A]("Q * (L.inv(x) * L.inv(x))")
					quotientIn := c.Have(
						"Q · inv(x)², a member of k[1/x], lies in the overlap",
						"Q * (L.inv(x) * L.inv(x)) ∈ «curveLaurent»",
						By(inChart1[1], invInKs, ksInOverlap, comm_ring.MulIn.Read(ringKs), set_basic.SubsetDef))
					m, clearedQ := c.ObtainAs[Nat](
						"so a power xᵐ carries it into k[x]",
						"∃m:num. monoid_pow(L.mul, L.one, x, m) * (Q * (L.inv(x) * L.inv(x))) ∈ «curveKx»",
						By(quotientIn, ring_away.RingAwayMember.At(fieldOps, kx, x, quotient)))
					powersKx := c.Have(
						"xⁿ and xᵐ lie in k[x]",
						"monoid_pow(L.mul, L.one, x, n) ∈ «curveKx» ∧ monoid_pow(L.mul, L.one, x, m) ∈ «curveKx»",
						By(xInKx, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringKx))))
					xToN, xToM := comm_monoid.PowIn.Read(powersL).At(xm, n), comm_monoid.PowIn.Read(powersL).At(xm, m)
					invToN, invToM :=
						comm_monoid.PowIn.Read(powersL).At(invXm, n), comm_monoid.PowIn.Read(powersL).At(invXm, m)
					members := c.Have(
						"p, q, P and Q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier ∧ P ∈ L.carrier ∧ Q ∈ L.carrier",
						BySets(
							inChart0[0],
							inChart0[1],
							inChart1[0],
							inChart1[1],
							kxInOverlap,
							ksInOverlap,
							comm_ring.SubringSubset.Read(line[4])))
					agree := c.Have(
						"the two expansions are one member",
						"p + q * y = P + Q * «curveU»",
						By(Normalized, inChart0[2], inChart1[2]))
					cleared := c.Have(
						"multiplied by xⁿ · xᵐ, both expansions have their coefficients in k[x]",
						"«weierstrassGlobalSectionsClearedP0» + «weierstrassGlobalSectionsClearedQ0» * y = "+
							"«weierstrassGlobalSectionsClearedP1» + «weierstrassGlobalSectionsClearedQ1» * y",
						ByArith(
							ringL,
							members,
							ym,
							invXm,
							xToN,
							xToM,
							Scaled(c.TermAs[A]("monoid_pow(L.mul, L.one, x, n) * monoid_pow(L.mul, L.one, x, m)"), agree)))
					coefficients := c.Have(
						"the four coefficients lie in k[x]",
						"«weierstrassGlobalSectionsClearedP0» ∈ «curveKx» ∧ "+
							"«weierstrassGlobalSectionsClearedQ0» ∈ «curveKx» ∧ "+
							"«weierstrassGlobalSectionsClearedP1» ∈ «curveKx» ∧ "+
							"«weierstrassGlobalSectionsClearedQ1» ∈ «curveKx»",
						By(powersKx, inChart0[0], inChart0[1], clearedP, clearedQ, comm_ring.MulIn.Read(ringKx)))
					differences := c.Have(
						"so do their differences, k[x] being a ring",
						"«weierstrassGlobalSectionsDifferenceAtOne» ∈ «curveKx» ∧ "+
							"«weierstrassGlobalSectionsDifferenceAtY» ∈ «curveKx»",
						By(coefficients, comm_ring.SubIn.Read(ringKx)))
					vanishing := c.Have(
						"and the cleared expansions differ by a vanishing combination of 1 and y",
						"«weierstrassGlobalSectionsDifferenceAtOne» + «weierstrassGlobalSectionsDifferenceAtY» * y = "+
							"L.zero",
						ByArith(ringL, members, ym, invXm, xToN, xToM, cleared))
					unique := c.Conjuncts(
						c.Have(
							"1 and y being independent over k[x], both differences are zero",
							"«weierstrassGlobalSectionsDifferenceAtOne» = L.zero ∧ "+
								"«weierstrassGlobalSectionsDifferenceAtY» = L.zero",
							By(
								datum,
								differences,
								vanishing,
								ChartZeroCoefficientsVanish.Read(L).At(
									k,
									x,
									y,
									a,
									b,
									c.TermAs[A]("«weierstrassGlobalSectionsDifferenceAtOne»"),
									c.TermAs[A]("«weierstrassGlobalSectionsDifferenceAtY»")))),
						"xⁿxᵐ · p − xᵐ · xⁿ · P is zero",
						"xⁿxᵐ · q − xⁿ · xᵐ · Q · inv(x)² is zero")

					// Cancelling xⁿ · xᵐ, which inv(x)ⁿ · inv(x)ᵐ inverts.
					powerUnits := c.Conjuncts(
						c.Have(
							"xⁿ · inv(x)ⁿ and xᵐ · inv(x)ᵐ are one, as x · inv(x) is",
							"monoid_pow(L.mul, L.one, x, n) * «weierstrassGlobalSectionsInvXn» = L.one ∧ "+
								"monoid_pow(L.mul, L.one, x, m) * «weierstrassGlobalSectionsInvXm» = L.one",
							By(
								unit,
								comm_monoid.PowInverseOn.Read(powersL).At(xm, invXm, n),
								comm_monoid.PowInverseOn.Read(powersL).At(xm, invXm, m))),
						"xⁿ · inv(x)ⁿ = one",
						"xᵐ · inv(x)ᵐ = one")
					inverse := c.Have(
						"so inv(x)ⁿ · inv(x)ᵐ inverts xⁿ · xᵐ",
						"monoid_pow(L.mul, L.one, x, n) * "+
							"monoid_pow(L.mul, L.one, x, m) * "+
							"(«weierstrassGlobalSectionsInvXn» * «weierstrassGlobalSectionsInvXm») = "+
							"L.one",
						ByArith(
							ringL,
							xToN,
							xToM,
							invToN,
							invToM,
							Scaled(
								c.TermAs[A]("monoid_pow(L.mul, L.one, x, m) * «weierstrassGlobalSectionsInvXm»"), powerUnits[0]),
							powerUnits[1]))
					scale := c.TermAs[A]("«weierstrassGlobalSectionsInvXn» * «weierstrassGlobalSectionsInvXm»")
					difference := c.Have(
						"cancelling xⁿ · xᵐ, p − P vanishes",
						"p - P = L.zero",
						ByArith(
							ringL,
							members,
							xToN,
							xToM,
							invToN,
							invToM,
							Scaled(scale, unique[0]),
							Scaled(c.TermAs[A]("p - P"), inverse)))
					constantTerms := c.Have(
						"so p = P",
						"p = P",
						CalcEq(
							Leg(
								c.TermAs[A]("P + (p - P)"),
								"P plus the difference p − P",
								ByArith(ringL, members)),
							FinalLeg(
								"which is zero",
								ByArith(ringL, members, difference))))
					coefficientOfY := c.Have(
						"and q = Q · inv(x)²",
						"q = Q * (L.inv(x) * L.inv(x))",
						ByArith(
							ringL,
							members,
							invXm,
							xToN,
							xToM,
							invToN,
							invToM,
							Scaled(scale, unique[1]),
							Scaled(c.TermAs[A]("q - Q * (L.inv(x) * L.inv(x))"), inverse)))

					pInKs := c.Have(
						"p, being P, lies in k[1/x]",
						"p ∈ «curveKs»",
						constantTerms.Rw(),
						By(inChart1[0]))
					pConstant := c.Have(
						"so p, in k[x] as well, is a constant",
						"p ∈ k",
						By(constants, inChart0[0], pInKs))
					qInKs := c.Have(
						"q = Q · inv(x)² lies in k[1/x]",
						"q ∈ «curveKs»",
						coefficientOfY.Rw(),
						By(inChart1[1], invInKs, comm_ring.MulIn.Read(ringKs)))
					qConstant := c.Have(
						"so q, in k[x] as well, is a constant",
						"q ∈ k",
						By(constants, inChart0[1], qInKs))
					qZero := c.Have(
						"q is zero: otherwise x = Q · inv(x) · inv(q) would lie in k[1/x] and so be a constant",
						"q = L.zero",
						Derive(func(d *Argument) {
							nonzeroQ := d.SupposeNot()
							qm := d.MemberOf[on.L](q, d.Have(
								"q lies in L",
								"q ∈ L.carrier",
								By(members)))
							qUnit := d.Have(
								"q · inv(q) = one",
								"q * L.inv(q) = L.one",
								By(nonzeroQ, field.MulRightInverseOn.Read(L).At(qm)))
							invQInKs := d.Have(
								"inv(q) lies in the subfield k, so in k[1/x]",
								"L.inv(q) ∈ «curveKs»",
								By(subK, qConstant, kInKs, field.SubfieldInv, set_basic.SubsetDef))
							xIs := d.Have(
								"x = x · q · inv(q) = x · Q · inv(x)² · inv(q) = Q · inv(x) · inv(q)",
								"x = Q * (L.inv(x) * L.inv(q))",
								ByArith(
									ringL,
									xm,
									members,
									invXm,
									field.InvIn.Read(L).At(qm),
									Scaled(x, qUnit),
									Scaled(d.TermAs[A]("x * L.inv(q)"), coefficientOfY),
									Scaled(d.TermAs[A]("Q * (L.inv(x) * L.inv(q))"), unit)))
							xInKs := d.Have(
								"so x lies in k[1/x]",
								"x ∈ «curveKs»",
								By(xIs, inChart1[1], invInKs, invQInKs, comm_ring.MulIn.Read(ringKs)))
							xConstant := d.Have(
								"and, lying in k[x], x is a constant",
								"x ∈ k",
								By(constants, xInKx, xInKs))
							d.Show(
								"a constant is algebraic over k, and x is not",
								By(transcendental, subK, xConstant, algebraic_element.MemberAlgebraic.Read(L).At(k, x)))
						}))
					collapse := c.Have(
						"so p + q·y is p",
						"p + q * y = p",
						CalcEq(
							Leg(
								c.TermAs[A]("p + L.zero * y"),
								"q is zero",
								By(Normalized, qZero)),
							FinalLeg(
								"and zero · y vanishes",
								ByArith(ringL, members, ym))))
					c.Show(
						"z is the constant p",
						inChart0[2].Rw(),
						collapse.Rw(),
						By(pConstant))
				}))
			inside := arg.Have(
				"so the charts meet inside k",
				"«curveChart0» ∩ «curveChart1» ⊆ k",
				By(common, set_basic.SubsetDef))
			holds := arg.Have(
				"and their meet holds k, which lies in k[x] ⊆ chart 0 and in k[1/x] ⊆ chart 1",
				"k ⊆ «curveChart0» ∩ «curveChart1»",
				By(
					datum,
					kInKx,
					WeierstrassBasisZero.Read(L).At(k, x, y, a, b),
					kInKs,
					WeierstrassBasisOne.Read(L).At(k, x, y, a, b),
					set_order.SubsetInter.At(k, chart0, chart1),
					set_order.SubsetTrans.At(k, kx, chart0),
					set_order.SubsetTrans.At(k, ks, chart1)))
			arg.Show(
				"the charts meet in k",
				By(
					inside,
					holds,
					set_order.SubsetAntisym.At(arg.TermAs[Set[A]]("«curveChart0» ∩ «curveChart1»"), k)))
		}),
})}

// WeierstrassBiaffine — the two charts of a Weierstrass datum, glued
// along A₀₁ = A₀[1/x], form a biaffine datum with x and inv(x). x is
// not zero, being transcendental, so it is a unit with inverse inv(x).
// A₀[1/x] is a subring of L holding chart 0 and inv(x)
// (RingAwaySubring), and it is A₁[x] (WeierstrassOverlap), which holds
// chart 1. Computed in the ring of A₀₁, chart 0 with x inverted and
// chart 1 with inv(x) inverted are what they are in L, since A₀₁ holds
// both inverses (RingAwayInSubring): A₀[1/x] and A₁[x], A₀₁ both times.
var WeierstrassBiaffine = weierstrassBiaffineThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassBiaffine",
	Key:  "prop_c8a374229035f38b",
	Reading: "Of the transcendence of x only x ≠ zero is read: x and inv(x) are the elements " +
		"the two charts invert, and A₀₁ is the ring each chart becomes with its element inverted.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "biaffine(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    x, " +
			"    L.inv(x))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], h Fact) {
			subK := WeierstrassSubfield.Read(h)
			xm := arg.MemberOf[on.L](x, WeierstrassXInField.Read(h).AsFact())
			invX := field.InvIn.Read(L).At(xm)
			invertible := arg.Conjuncts(
				GroupPremises(h, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")
			unit, unitLeft := invertible[2], invertible[3]

			// The charts: subrings of L holding k[x] and k[1/x], so x and inv(x).
			chart0 := arg.Conjuncts(
				GroupPremises(h, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"chart 0 holds k[x]",
				"chart 0 is free over k[x] on one and y",
				"one is not y")
			chart1 := arg.Conjuncts(
				GroupPremises(h, WeierstrassBasisOne.Read(L).At(k, x, y, a, b)),
				"chart 1 is a subring of L",
				"chart 1 holds k[1/x]",
				"chart 1 is free over k[1/x] on one and u",
				"one is not u")
			chart0Subring, kxInChart0 := chart0[0], chart0[1]
			chart1Subring, ksInChart1 := chart1[0], chart1[1]
			xInChart0 := arg.Have(
				"x lies in k[x], so in chart 0",
				"x ∈ «curveChart0»",
				BySets(kxInChart0, subK, algebraic_element.PolynomialImageRing.Read(L).At(k, xm)))
			invInChart1 := arg.Have(
				"and inv(x) in k[1/x], so in chart 1",
				"L.inv(x) ∈ «curveChart1»",
				BySets(ksInChart1, subK, algebraic_element.PolynomialImageRing.Read(L).At(k, invX)))

			// A₀₁ = A₀[1/x]: a subring of L holding chart 0 and inv(x), and A₁[x] as well, so it holds chart 1.
			fieldRing := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			ring := field.RingOn.Read(L)
			chartZero := arg.TermAs[Set[A]]("«curveChart0»")
			chartOne := arg.TermAs[Set[A]]("«curveChart1»")
			overlapSet := arg.TermAs[Set[A]]("«curveOverlap»")
			overlap := arg.Conjuncts(
				arg.Have(
					"A₀₁ is a subring of L holding chart 0 and the inverse inv(x) of x",
					"«curveChart0» ⊆ «curveOverlap» ∧ "+
						"subring(field_ring(L), «curveOverlap») ∧ "+
						"L.inv(x) ∈ «curveOverlap»",
					By(
						ring_away.RingAwaySubring.At(fieldRing, chartZero, x),
						ring,
						chart0Subring,
						xInChart0,
						invX,
						unit)),
				"chart 0 lies in A₀₁",
				"A₀₁ is a subring of L",
				"inv(x) lies in A₀₁")
			chart0InOverlap, overlapSubring, invInOverlap := overlap[0], overlap[1], overlap[2]
			overlapRing := arg.Have(
				"so A₀₁ is a ring",
				"comm_ring_on(«curveOverlapRing»)",
				By(overlapSubring, comm_ring.SubringRingOn.Read(ring).At(overlapSet)))
			glued := arg.Have(
				"the charts glue: A₀[1/x] = A₁[x]",
				"«curveOverlap» = ring_away(field_ring(L), «curveChart1», L.inv(x))",
				By(h, WeierstrassOverlap.Read(L).At(k, x, y, a, b)))
			chart1InOverlap := arg.Have(
				"chart 1 lies in A₁[x], which is A₀₁",
				"«curveChart1» ⊆ «curveOverlap»",
				glued.Rw(),
				By(ring_away.RingAwaySubring.At(fieldRing, chartOne, invX), ring, chart1Subring, invInChart1))
			xInOverlap := arg.Have(
				"x lies in A₀₁, as chart 0 does",
				"x ∈ «curveOverlap»",
				BySets(chart0InOverlap, xInChart0))

			// Inside the ring of A₀₁: each chart a subring, and each chart with its generator inverted.
			chart0Restricted := arg.Have(
				"chart 0 restricted from the ring of A₀₁ is chart 0 restricted from L",
				"restrict_ring(«curveOverlapRing», «curveChart0») = restrict_ring(field_ring(L), «curveChart0»)",
				Unfold(module_record.RestrictRingDef))
			chart1Restricted := arg.Have(
				"and likewise chart 1",
				"restrict_ring(«curveOverlapRing», «curveChart1») = restrict_ring(field_ring(L), «curveChart1»)",
				Unfold(module_record.RestrictRingDef))
			chart0InRing := arg.Have(
				"chart 0, a ring lying in A₀₁, is a subring of the ring of A₀₁",
				"subring(«curveOverlapRing», «curveChart0»)",
				By(
					chart0Subring,
					comm_ring.SubringRingOn.Read(ring).At(chartZero),
					chart0InOverlap,
					chart0Restricted,
					comm_ring.SubringRingOn.Read(overlapRing).At(chartZero)))
			chart1InRing := arg.Have(
				"and so is chart 1",
				"subring(«curveOverlapRing», «curveChart1»)",
				By(
					chart1Subring,
					comm_ring.SubringRingOn.Read(ring).At(chartOne),
					chart1InOverlap,
					chart1Restricted,
					comm_ring.SubringRingOn.Read(overlapRing).At(chartOne)))
			awayFromX := arg.Have(
				"computed in the ring of A₀₁, chart 0 with x inverted is A₀[1/x], which is A₀₁",
				"ring_away(«curveOverlapRing», «curveChart0», x) = «curveOverlap»",
				By(
					ring_away.RingAwayInSubring.At(fieldRing, overlapSet, chartZero, x, invX),
					ring,
					overlapSubring,
					xInOverlap,
					chart0InOverlap,
					invInOverlap,
					unit))
			awayFromInv := arg.Have(
				"and chart 1 with inv(x) inverted is A₁[x]",
				"ring_away(«curveOverlapRing», «curveChart1», L.inv(x)) = "+
					"ring_away(field_ring(L), «curveChart1», L.inv(x))",
				By(
					ring_away.RingAwayInSubring.At(fieldRing, overlapSet, chartOne, invX, x),
					ring,
					overlapSubring,
					invInOverlap,
					chart1InOverlap,
					xInOverlap,
					unitLeft))
			arg.Show(
				"so the ring of A₀₁, the two charts, x and inv(x) form a biaffine datum, A₁[x] being A₀₁",
				By(
					lattice_pair.BiaffineDef.At(
						arg.TermAs[module_record.RingOps[A]]("«curveOverlapRing»"), chartZero, chartOne, x, invX),
					overlapRing,
					chart0InRing,
					chart1InRing,
					xInChart0,
					invInChart1,
					unit,
					awayFromX,
					awayFromInv,
					glued))
		}),
})}

// WeierstrassIsCurve — a Weierstrass datum is a curve over the
// projective line: x is the line's coordinate, the charts are chart 0
// and chart 1, the overlap is A₀₁ = A₀[1/x]. Every clause of the curve
// is in hand: the subfield, x and its transcendence are the datum's; L
// is the fraction field of chart 0, which lies in L, each member of L
// being a quotient from chart 0 by the datum; the overlap lies in L, a
// member of it being a member of L; glued along it the charts are
// biaffine (WeierstrassBiaffine); they hold k[x] and k[1/x] and are free
// over them on the two-element sets {one, y} and {one, u}; and they meet
// in k (WeierstrassGlobalSections).
var WeierstrassIsCurve = weierstrassIsCurveThm{family.Add(registry.ProofEntry{
	Name:    "WeierstrassIsCurve",
	Key:     "prop_df545b33bc785da4",
	Reading: "The degree over the line is two, the basis {one, y}.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "curve_over_line(L, " +
			"    k, " +
			"    x, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], h Fact) {
			chart0 := arg.Conjuncts(
				GroupPremises(h, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"chart 0 holds k[x]",
				"chart 0 is free over k[x] on one and y",
				"one is not y")
			chart1 := arg.Conjuncts(
				GroupPremises(h, WeierstrassBasisOne.Read(L).At(k, x, y, a, b)),
				"chart 1 is a subring of L",
				"chart 1 holds k[1/x]",
				"chart 1 is free over k[1/x] on one and u",
				"one is not u")
			kxInChart0, ksInChart1 := chart0[1], chart1[1]
			inField := arg.Have(
				"the overlap A₀₁ = A₀[1/x] lies in L: its members are "+
					"the members of L that a power of x carries into chart 0",
				"«curveOverlap» ⊆ L.carrier",
				Unfold(ring_away.RingAwayDef),
				BySets())

			// The bases {one, y} and {one, u}: one point added to a singleton, so finite.
			one, u := arg.TermAs[A]("L.one"), arg.TermAs[A]("«curveU»")
			basis0 := arg.Have(
				"chart 0 has a finite basis over k[x], the two-element {one, y}",
				"∃E:set(A). "+
					"    finite(E) ∧ "+
					"    module_basis(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, x)), "+
					"        restrict_module(regular_module(field_ring(L)), «curveChart0»), "+
					"        E)",
				Witness(arg.TermAs[Set[A]]("{L.one, y}")),
				By(
					chart0[2],
					finite_set.FiniteInsert.At(one, arg.TermAs[Set[A]]("{y}")),
					finite_set.FiniteSing.At(y)))
			basis1 := arg.Have(
				"chart 1 has a finite basis over k[1/x], the two-element {one, u}",
				"∃E:set(A). "+
					"    finite(E) ∧ "+
					"    module_basis(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(x))), "+
					"        restrict_module(regular_module(field_ring(L)), «curveChart1»), "+
					"        E)",
				Witness(arg.TermAs[Set[A]]("{L.one, «curveU»}")),
				By(
					chart1[2],
					finite_set.FiniteInsert.At(one, arg.TermAs[Set[A]]("{«curveU»}")),
					finite_set.FiniteSing.At(u)))

			// Glued along A₀₁ the charts are biaffine, and they meet in k.
			biaffine := arg.Simplified(GroupPremises(h, WeierstrassBiaffine.Read(L).At(k, x, y, a, b)))
			sections := arg.Simplified(GroupPremises(h, WeierstrassGlobalSections.Read(L).At(k, x, y, a, b)))
			subfield, xInL, transcendental :=
				WeierstrassSubfield.Read(h), WeierstrassXInField.Read(h), WeierstrassTranscendental.Read(h)
			chartZero := arg.TermAs[Set[A]]("«curveChart0»")
			fractionField := arg.Have(
				"L is the fraction field of chart 0: chart 0 lies in L, "+
					"and each member of L is a quotient of two members of it",
				"fraction_field_carrier(field_ring(L), «curveChart0»)",
				By(
					comm_ring.SubringSubset.Read(chart0[0]),
					WeierstrassFractionField.Read(h),
					field.FractionFieldCarrierDef.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), chartZero)))
			arg.Show(
				"every clause of a curve over the line is in hand",
				By(
					algebraic_curve.CurveOverLineDef.At(arg.TermAs[field.FieldOps[A]]("L"), k, x, chartZero,
						arg.TermAs[Set[A]]("«curveChart1»"), arg.TermAs[Set[A]]("«curveOverlap»")),
					subfield,
					xInL,
					transcendental,
					inField,
					biaffine,
					kxInChart0,
					ksInChart1,
					basis0,
					basis1,
					sections,
					fractionField))
		}),
})}

// WeierstrassOverlapCoordinates — the overlap A₀[1/x] is k[x, 1/x] · 1 ⊕
// k[x, 1/x] · y: its members are the p + q·y with p and q in k[x, 1/x],
// and each is so in one way. The basis 1, y of chart 0 over k[x] is a
// basis of the overlap over k[x, 1/x] (BasisSpansOverlap), and a member,
// the combination of its two coordinates p and q, is p + q·y
// (linear_independence.CombinationPair). Two expansions p + q·y =
// p₁ + q₁·y differ by (p − p₁) + (q − q₁)·y = zero, so p = p₁ and q = q₁,
// 1 and y being independent over k[x, 1/x]
// (WeierstrassLaurentCoefficients).
var WeierstrassOverlapCoordinates = weierstrassOverlapCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassOverlapCoordinates",
	Key:  "prop_16ec1827a42f702",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∀z:A. " +
			"    z ∈ «curveOverlap» ⇔ ∃p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ z = p + q * y) ∧ " +
			"(∀p q p₁ q₁:A. " +
			"    p ∈ «curveLaurent» ∧ " +
			"    q ∈ «curveLaurent» ∧ " +
			"    p₁ ∈ «curveLaurent» ∧ " +
			"    q₁ ∈ «curveLaurent» ∧ " +
			"    p + q * y = p₁ + q₁ * y ⇒ " +
			"    p = p₁ ∧ q = q₁)",
		Abbrev: Abbrev{
			{Name: "curveOverlapCoordinate", Text: "module_basis_coordinates( " +
				"    restrict_ring(field_ring(L), «curveLaurent»), " +
				"    restrict_module(regular_module(field_ring(L)), «curveOverlap»), " +
				"    {L.one, y})"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")
			overlap := arg.TermAs[Set[A]]("«curveOverlap»")
			one, pair, single :=
				arg.TermAs[A]("L.one"), arg.TermAs[Set[A]]("{L.one, y}"), arg.TermAs[Set[A]]("{y}")
			ring := field.RingOn.Read(L)
			curve := arg.Simplified(GroupPremises(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := arg.Simplified(
				GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)))
			chart := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"k[x] lies in chart 0",
				"1 and y are a basis of chart 0 over k[x]",
				"one is not y")
			onLaurent := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingModuleOn.Read(L).At(k, chart0, chart1, overlap, x)),
				"k[x, 1/x] is a subring of L",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			laurentIn, overlapModule := onLaurent[1], onLaurent[3]
			laurentRing := arg.Have(
				"k[x, 1/x] is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «curveLaurent»))",
				By(onLaurent[0], comm_ring.SubringRingOn.Read(ring).At(arg.TermAs[Set[A]]("«curveLaurent»"))))
			overlapSubring := arg.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), «curveOverlap»)",
				By(line))
			overlapRing := arg.Have(
				"so it is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveOverlap»))",
				By(overlapSubring, comm_ring.SubringRingOn.Read(ring).At(overlap)))
			inField := arg.Have(
				"and lies in L",
				"«curveOverlap» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(overlapSubring)))
			basis := arg.Have(
				"1 and y are a basis of the overlap over k[x, 1/x]",
				"module_basis(restrict_ring(field_ring(L), «curveLaurent»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveOverlap»), "+
					"    {L.one, y})",
				By(curve, chart[2], algebraic_curve.BasisSpansOverlap.Read(L).At(k, chart0, chart1, overlap, x)))
			independent := arg.Conjuncts(
				arg.Unfolded(basis, linear_independence.ModuleBasisDef),
				"1 and y are independent",
				"they span the overlap")[0]
			basisIn := arg.Have(
				"1 and y lie in the overlap",
				"L.one ∈ «curveOverlap» ∧ y ∈ «curveOverlap»",
				BySets(linear_independence.IndependentInCarrier.Read(independent)))
			pairIn := arg.Conjuncts(
				basisIn,
				"1 lies in the overlap",
				"so does y")
			oneM, yM := proof.MemberOf(one, pairIn[0]), proof.MemberOf(y, pairIn[1])
			pairFinite := arg.Have(
				"{1, y} is finite",
				"finite({L.one, y})",
				By(finite_set.FiniteSing.At(y), finite_set.FiniteInsert.At(one, single)))
			inPair := arg.Have(
				"1 and y lie in {1, y}",
				"L.one ∈ {L.one, y} ∧ y ∈ {L.one, y}",
				BySets())

			pairSum := arg.Have(
				"a combination of 1 and y with coefficients in k[x, 1/x] is its two terms",
				Statement{
					Binders: "∀c:(A → A).",
					Hypotheses: []string{
						"c(L.one) ∈ «curveLaurent»",
						"c(y) ∈ «curveLaurent»",
					},
					Conclusion: "module_sum(L.add, L.zero, {L.one, y}, λe:A. c(e) * e) = c(L.one) + c(y) * y",
				},
				Derive(func(sub *Argument) {
					c := sub.FixAs[Fun[A, A]]("c")
					coefficients := sub.Assume()
					sum := sub.Have(
						"a combination of the distinct members 1 and y of the overlap is its two terms",
						"module_sum(L.add, L.zero, {L.one, y}, λe:A. c(e) * e) = c(L.one) * L.one + c(y) * y",
						By(coefficients, chart[3], linear_independence.CombinationPair.Read(overlapModule).At(oneM, yM, c)))
					inL := sub.Have(
						"the coefficient at 1 lies in L",
						"c(L.one) ∈ L.carrier",
						BySets(coefficients, laurentIn, inField))
					unit := sub.Have(
						"and c(1) · 1 = c(1)",
						"c(L.one) * L.one = c(L.one)",
						ByArith(ring, inL))
					sub.Show(
						"so the combination is c(1) + c(y) · y",
						By(sum, unit))
				}))

			spans := arg.Have(
				"a member of the overlap is p + q·y, its coordinates in the basis 1, y lying in k[x, 1/x]",
				"∀z:A. z ∈ «curveOverlap» ⇒ ∃p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ z = p + q * y",
				Derive(func(sub *Argument) {
					z := sub.FixAs[A]("z")
					zIn := sub.Assume()
					coordinates := sub.Conjuncts(
						GroupPremises(
							pairFinite,
							basis,
							module_dimension.BasisCoordinatesSpec.Read(overlapModule).At(pair, proof.MemberOf(z, zIn))),
						"the coordinates of z lie in k[x, 1/x]",
						"they vanish off {1, y}",
						"they expand z")
					c := sub.TermAs[Fun[A, A]](
						"module_basis_coordinates(restrict_ring(field_ring(L), «curveLaurent»), " +
							"    restrict_module(regular_module(field_ring(L)), «curveOverlap»), " +
							"    {L.one, y}, " +
							"    z)")
					inLaurent := sub.Have(
						"the coordinates at 1 and at y lie in k[x, 1/x]",
						"«curveOverlapCoordinate»(z, L.one) ∈ «curveLaurent» ∧ "+
							"«curveOverlapCoordinate»(z, y) ∈ «curveLaurent»",
						By(coordinates[0], inPair))
					sub.Take(sub.TermAs[A]("«curveOverlapCoordinate»(z, L.one)"))
					sub.Take(sub.TermAs[A]("«curveOverlapCoordinate»(z, y)"))
					sub.Show(
						"z is the combination of its coordinates",
						By(inLaurent, coordinates[2], pairSum.At(c)))
				}))
			members := arg.Have(
				"and every p + q·y with p and q in k[x, 1/x] lies in the overlap, a ring holding k[x, 1/x] and y",
				"∀p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ⇒ p + q * y ∈ «curveOverlap»",
				Derive(func(sub *Argument) {
					p := sub.FixAs[A]("p")
					sub.FixAs[A]("q")
					coefficients := sub.Assume()
					inOverlap := sub.Have(
						"p and q lie in the overlap",
						"p ∈ «curveOverlap» ∧ q ∈ «curveOverlap»",
						BySets(coefficients, laurentIn))
					pIn := sub.Have(
						"p lies in the overlap",
						"p ∈ «curveOverlap»",
						By(inOverlap))
					product := sub.Have(
						"so does q · y",
						"q * y ∈ «curveOverlap»",
						By(inOverlap, basisIn, comm_ring.MulIn.Read(overlapRing)))
					sub.Show(
						"so does the sum",
						By(comm_ring.AddIn.Read(overlapRing).At(
							proof.MemberOf(p, pIn), proof.MemberOf(sub.TermAs[A]("q * y"), product))))
				}))

			unique := arg.Have(
				"two expansions of one member have the same coefficients",
				Statement{
					Binders: "∀p q p₁ q₁:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
						"p₁ ∈ «curveLaurent»",
						"q₁ ∈ «curveLaurent»",
						"p + q * y = p₁ + q₁ * y",
					},
					Conclusion: "p = p₁ ∧ q = q₁",
				},
				Derive(func(d *Argument) {
					d.FixAs[A]("p")
					d.FixAs[A]("q")
					d.FixAs[A]("p₁")
					d.FixAs[A]("q₁")
					parts := d.Conjuncts(
						d.Assume(),
						"p lies in k[x, 1/x]",
						"q lies in k[x, 1/x]",
						"p₁ lies in k[x, 1/x]",
						"q₁ lies in k[x, 1/x]",
						"the two expansions agree")
					inL := d.Have(
						"the four coefficients and y lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier ∧ p₁ ∈ L.carrier ∧ q₁ ∈ L.carrier ∧ y ∈ L.carrier",
						BySets(parts[0], parts[1], parts[2], parts[3], basisIn, laurentIn, inField))
					differences := d.Have(
						"p − p₁ and q − q₁ lie in k[x, 1/x], a ring",
						"p - p₁ ∈ «curveLaurent» ∧ q - q₁ ∈ «curveLaurent»",
						By(parts[0], parts[1], parts[2], parts[3], comm_ring.SubIn.Read(laurentRing)))
					vanishing := d.Have(
						"the two expansions differ by (p − p₁) + (q − q₁)·y = zero",
						"(p - p₁) + (q - q₁) * y = L.zero",
						ByArith(ring, inL, parts[4]))
					zeros := d.Have(
						"so both differences are zero, 1 and y being independent over k[x, 1/x]",
						"p - p₁ = L.zero ∧ q - q₁ = L.zero",
						By(
							datum,
							differences,
							vanishing,
							WeierstrassLaurentCoefficients.Read(L).At(
								k, x, y, a, b, d.TermAs[A]("p - p₁"), d.TermAs[A]("q - q₁"))))
					d.Show(
						"so p = p₁ and q = q₁",
						ByArith(ring, inL, zeros))
				}))
			arg.Show(
				"the overlap is k[x, 1/x] · 1 ⊕ k[x, 1/x] · y",
				By(spans, members, unique))
		}),
})}

// WeierstrassModelExists — the field of fractions of the Weierstrass
// ring over a field k is a field holding a Weierstrass datum: the images
// of k, of the two variables and of a and b.
var WeierstrassModelExists = weierstrassModelExistsThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassModelExists",
	Key:  "prop_6ae5d1cd368c7bd1",
	Reading: "The ring is a domain for every a and b (WeierstrassRingDomain). x ≠ y is " +
		"load-bearing: at x = y the ring is k[y]/(y² − y³ − ay − b), finite-dimensional " +
		"over k, and the image of the variable is algebraic over the image of k. The field " +
		"lives on the fractions of cosets of the free algebra, a type of its own.",
	Deps: []registry.EntryLike{
		WeierstrassDef,
		WeierstrassChartZeroDef,
		WeierstrassRingDomain,
		ring_localization.FractionField,
		ring_localization.ToFractionInjective,
		ring_localization.ToFractionDef,
		ring_localization.FractionFieldDef,
		free_algebra.FreeAlgebraMonicQuadraticReduction,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.PolynomialOneVariableInjective,
		cotangent_examples.KoszulQuotientIdealQuotient,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.CosetEqIff,
		field.SubfieldDef,
		algebraic_element.AlgebraicOverDef,
		algebraic_element.PolynomialImageDef,
		WeierstrassRingDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseEmbeddingHost,
	},
	Build: family.Card(Statement{
		Binders: "∀k:field_on(A). ∀x y:U. ∀a b:A.",
		Hypotheses: []string{
			"cotangent_universe(field_ring(k), 𝕌⟨A:U⟩)",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"x ≠ y",
		},
		Conclusion: "field_on(mk_field(fraction_add(weierstrass_ring(field_ring(k), x, y, a, b).add, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_zero(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_neg(weierstrass_ring(field_ring(k), x, y, a, b).neg, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_mul(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_one(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_sub(weierstrass_ring(field_ring(k), x, y, a, b).add, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).neg, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_inv(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_div(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_field(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier))) ∧ " +
			"weierstrass(mk_field(fraction_add(weierstrass_ring(field_ring(k), x, y, a, b).add, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_zero(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_neg(weierstrass_ring(field_ring(k), x, y, a, b).neg, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_mul(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_one(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_sub(weierstrass_ring(field_ring(k), x, y, a, b).add, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).neg, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_inv(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_div(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}), " +
			"        fraction_field(weierstrass_ring(field_ring(k), x, y, a, b).zero, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier)), " +
			"    {to_fraction(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"            weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"            {weierstrass_ring(field_ring(k), x, y, a, b).zero}, " +
			"            koszul_projection(universe_algebra_ring(field_ring(k), {x, y}), " +
			"                weierstrass_relation(field_ring(k), x, y, a, b), " +
			"                universe_algebra_const(field_ring(k), c))) | " +
			"        c:A | " +
			"        c ∈ k.carrier}, " +
			"    to_fraction(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"        {weierstrass_ring(field_ring(k), x, y, a, b).zero}, " +
			"        koszul_projection(universe_algebra_ring(field_ring(k), {x, y}), " +
			"            weierstrass_relation(field_ring(k), x, y, a, b), " +
			"            universe_algebra_var(field_ring(k), x))), " +
			"    to_fraction(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"        {weierstrass_ring(field_ring(k), x, y, a, b).zero}, " +
			"        koszul_projection(universe_algebra_ring(field_ring(k), {x, y}), " +
			"            weierstrass_relation(field_ring(k), x, y, a, b), " +
			"            universe_algebra_var(field_ring(k), y))), " +
			"    to_fraction(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"        {weierstrass_ring(field_ring(k), x, y, a, b).zero}, " +
			"        koszul_projection(universe_algebra_ring(field_ring(k), {x, y}), " +
			"            weierstrass_relation(field_ring(k), x, y, a, b), " +
			"            universe_algebra_const(field_ring(k), a))), " +
			"    to_fraction(weierstrass_ring(field_ring(k), x, y, a, b).mul, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).one, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier, " +
			"        weierstrass_ring(field_ring(k), x, y, a, b).carrier ∖ " +
			"        {weierstrass_ring(field_ring(k), x, y, a, b).zero}, " +
			"        koszul_projection(universe_algebra_ring(field_ring(k), {x, y}), " +
			"            weierstrass_relation(field_ring(k), x, y, a, b), " +
			"            universe_algebra_const(field_ring(k), b))))",
	},
		"the ring is a domain (WeierstrassRingDomain, a field being a domain), so its fractions "+
			"form a field (FractionField) into which it embeds one-to-one (ToFractionInjective); c "+
			"↦ the image of the constant c is a one-to-one ring map from k (FreeAlgebraConstHom), "+
			"so its image is a subfield holding the images of a and b, and the relation holds of "+
			"the images (IdealQuotientProjection, KoszulQuotientIdealQuotient). Every class is p(x) "+
			"+ q(x)·y with p, q polynomials in x over k (FreeAlgebraMonicQuadraticReduction), so "+
			"the image of the ring is chart 0 of the images and every fraction r/d has d · (r/d) = "+
			"r (ToFractionDef); a polynomial over the image of k vanishing at the image of x is a "+
			"polynomial in x alone lying in the ideal of the relation, zero by the uniqueness half "+
			"of the reduction (PolynomialOneVariableInjective), so the image of x is transcendental"),
})}

// WeierstrassImageIsomorphism — in a field holding a Weierstrass datum,
// evaluation at x and y is an isomorphism of k-algebras from the
// Weierstrass ring over k onto chart 0.
var WeierstrassImageIsomorphism = weierstrassImageIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassImageIsomorphism",
	Key:  "prop_540669a17707d179",
	Reading: "The quotient of the free algebra and the chart inside the field are one " +
		"ring: whatever is proved of the Weierstrass ring — its Kähler differentials, its " +
		"cotangent complex — holds of chart 0 through this map. ξ ≠ η is load-bearing: at " +
		"ξ = η both variables are one class and no map sends them to the distinct x and " +
		"y. In the fraction field of the Weierstrass ring (WeierstrassModelExists) the " +
		"map is the embedding r ↦ r/1, which agrees with it on the generators.",
	Deps: []registry.EntryLike{
		WeierstrassDef,
		WeierstrassChartZeroDef,
		WeierstrassBasisZero,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraMonicQuadraticReduction,
		free_algebra.PolynomialOneVariableInjective,
		quotient_ring.QuotientFirstIso,
		cotangent_examples.KoszulQuotientIdealQuotient,
		simplicial_ring.UniverseEmbeddingHost,
		algebraic_element.EvalInjectiveTranscendental,
		ring_homomorphism.RingIsomorphismDef,
		WeierstrassRingDef,
		simplicial_ring.UniverseAlgebraRingDef,
		field.SubfieldFieldOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀ξ η:U.",
		Hypotheses: []string{
			"cotangent_universe(restrict_ring(field_ring(L), k), 𝕌⟨A:U⟩)",
			"weierstrass(L, k, x, y, a, b)",
			"ξ ≠ η",
		},
		Conclusion: "∃φ:(set(U) → A). " +
			"    ring_isomorphism(weierstrass_ring(restrict_ring(field_ring(L), k), ξ, η, a, b), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        φ) ∧ " +
			"    φ(koszul_projection(universe_algebra_ring(restrict_ring(field_ring(L), k), {ξ, η}), " +
			"            weierstrass_relation(restrict_ring(field_ring(L), k), ξ, η, a, b), " +
			"            universe_algebra_var(restrict_ring(field_ring(L), k), ξ))) = " +
			"    x ∧ " +
			"    φ(koszul_projection(universe_algebra_ring(restrict_ring(field_ring(L), k), {ξ, η}), " +
			"            weierstrass_relation(restrict_ring(field_ring(L), k), ξ, η, a, b), " +
			"            universe_algebra_var(restrict_ring(field_ring(L), k), η))) = " +
			"    y ∧ " +
			"    (∀c:A. " +
			"        c ∈ k ⇒ " +
			"        φ(koszul_projection(universe_algebra_ring(restrict_ring(field_ring(L), k), {ξ, η}), " +
			"                weierstrass_relation(restrict_ring(field_ring(L), k), ξ, η, a, b), " +
			"                universe_algebra_const(restrict_ring(field_ring(L), k), c))) = " +
			"        c)",
	},
		"evaluation of the free algebra at ξ ↦ x, η ↦ y with the coefficients kept is a ring map into "+
			"the field (FreeAlgebraEvalHom, FreeAlgebraEvalVar, FreeAlgebraEvalConst) killing the relation, "+
			"so it descends to the quotient (KoszulQuotientIdealQuotient, QuotientFirstIso); every class is "+
			"p(ξ) + q(ξ)·η (FreeAlgebraMonicQuadraticReduction), sent to p(x) + q(x)·y, so the image is "+
			"chart 0; a class sent to zero has p(x) = q(x) = zero (WeierstrassBasisZero), so p and q are "+
			"zero (EvalInjectiveTranscendental through PolynomialOneVariableInjective) and the class is zero"),
})}

// WeierstrassChartOneEmbeds — in a field holding a Weierstrass datum,
// the chart-one ring over k maps by s ↦ 1/x and u ↦ y/x², one-to-one,
// onto chart 1.
var WeierstrassChartOneEmbeds = weierstrassChartOneEmbedsThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartOneEmbeds",
	Key:  "prop_7c2be0f7a88fce08",
	Reading: "The relation u² = s + as³ + bs⁴ of the chart-one ring is the " +
		"Weierstrass relation divided by x⁴ (WeierstrassChartOneEquation). s ≠ " +
		"u is load-bearing, as ξ ≠ η is in WeierstrassImageIsomorphism.",
	Deps: []registry.EntryLike{
		WeierstrassDef,
		WeierstrassChartOneDef,
		WeierstrassChartOneEquation,
		WeierstrassBasisOne,
		weierstrassChartOneRingDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraMonicQuadraticReduction,
		free_algebra.PolynomialOneVariableInjective,
		quotient_ring.QuotientFirstIso,
		cotangent_examples.KoszulQuotientIdealQuotient,
		algebraic_element.EvalInjectiveTranscendental,
		ring_homomorphism.RingIsomorphismDef,
		WeierstrassIsCurve,
		algebraic_curve.CurveOverLineDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseEmbeddingHost,
		field.SubfieldFieldOn,
		algebraic_element.TranscendentalInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀s u:U.",
		Hypotheses: []string{
			"cotangent_universe(restrict_ring(field_ring(L), k), 𝕌⟨A:U⟩)",
			"weierstrass(L, k, x, y, a, b)",
			"s ≠ u",
		},
		Conclusion: "∃φ:(set(U) → A). " +
			"    ring_isomorphism(weierstrass_chart_one_ring(restrict_ring(field_ring(L), k), s, u, a, b), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        φ) ∧ " +
			"    φ(koszul_projection(universe_algebra_ring(restrict_ring(field_ring(L), k), {s, u}), " +
			"            weierstrass_chart_one_relation(restrict_ring(field_ring(L), k), s, u, a, b), " +
			"            universe_algebra_var(restrict_ring(field_ring(L), k), s))) = " +
			"    L.inv(x) ∧ " +
			"    φ(koszul_projection(universe_algebra_ring(restrict_ring(field_ring(L), k), {s, u}), " +
			"            weierstrass_chart_one_relation(restrict_ring(field_ring(L), k), s, u, a, b), " +
			"            universe_algebra_var(restrict_ring(field_ring(L), k), u))) = " +
			"    y * (L.inv(x) * L.inv(x)) ∧ " +
			"    (∀c:A. " +
			"        c ∈ k ⇒ " +
			"        φ(koszul_projection(universe_algebra_ring(restrict_ring(field_ring(L), k), {s, u}), " +
			"                weierstrass_chart_one_relation(restrict_ring(field_ring(L), k), s, u, a, b), " +
			"                universe_algebra_const(restrict_ring(field_ring(L), k), c))) = " +
			"        c)",
	},
		"evaluation of the free algebra at s ↦ inv(x), u ↦ y · inv(x)² with the coefficients "+
			"kept is a ring map into the field (FreeAlgebraEvalHom, FreeAlgebraEvalVar, "+
			"FreeAlgebraEvalConst) killing the chart relation (WeierstrassChartOneEquation), so it "+
			"descends to the quotient (KoszulQuotientIdealQuotient, QuotientFirstIso); every class "+
			"is p(s) + q(s)·u (FreeAlgebraMonicQuadraticReduction), sent to p(1/x) + q(1/x)·y/x², so "+
			"the image is chart 1; one-to-one by WeierstrassBasisOne and EvalInjectiveTranscendental "+
			"at inv(x), transcendental over k as x is (TranscendentalInverse)"),
})}

// ---------------------------------------------------------------------------
// Genus one
// ---------------------------------------------------------------------------

// StructurePairFree — the structure pair of the curve, read on the
// projective line along the basis (1, y), is O(0) · 1 ⊕ O(−2) · y: the
// free pair's chart 0 is the k[x]-span of one and y, which is chart 0, and
// its chart 1 the k[1/x]-span of x⁰ · one = one and x⁻² · y = u, which is
// chart 1 (fractional_ideal.SpanOneAndElement at each chart).
var StructurePairFree = structurePairFreeThm{family.Add(registry.ProofEntry{
	Name: "StructurePairFree",
	Key:  "prop_a83067625155edb8",
	Reading: "Chart 1 is k[1/x] · 1 + k[1/x] · x⁻²y, so along (1, y) the twists " +
		"are 0 and −2: the structure pair of the curve is O(0) ⊕ O(−2) over the " +
		"line, not a sum of equal twists. one ≠ y keeps the two twists apart " +
		"(WeierstrassBasisZero). From it H⁰ = k and H¹ is one-dimensional, H¹(O(−2)).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y)) = " +
			"projective_line_free_pair(L, " +
			"    k, " +
			"    x, " +
			"    {L.one, y}, " +
			"    λe:A. COND(e = L.one, int_of_num(0), -int_of_num(2)))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			subfield := WeierstrassSubfield.Read(datum)
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			ring := field.RingOn.Read(L)
			sm := field.InvIn.Read(L).At(xm)
			um := comm_ring.MulIn.Read(ring).At(ym, comm_ring.MulIn.Read(ring).At(sm, sm))
			polynomialsX := arg.TermAs[Set[A]]("polynomial_image(field_ring(L), k, x)")
			polynomialsS := arg.TermAs[Set[A]]("polynomial_image(field_ring(L), k, L.inv(x))")

			// The two charts as spans: chart 0 over k[x] on one and y, chart 1 over k[1/x] on one and u.
			chart0 := arg.Have(
				"chart 0 is the k[x]-span of one and y",
				"module_span(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, x)), "+
					"    regular_module(field_ring(L)), "+
					"    {L.one, y}) = "+
					"weierstrass_chart_zero(field_ring(L), k, x, y)",
				Unfold(WeierstrassChartZeroDef),
				By(
					subfield,
					algebraic_element.PolynomialImageRing.Read(L).At(k, xm),
					fractional_ideal.SpanOneAndElement.Read(L).At(polynomialsX, ym)))
			chart1 := arg.Have(
				"chart 1 is the k[1/x]-span of one and u = y · inv(x)²",
				"module_span(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(x))), "+
					"    regular_module(field_ring(L)), "+
					"    {L.one, y * (L.inv(x) * L.inv(x))}) = "+
					"weierstrass_chart_one(L, k, x, y)",
				Unfold(WeierstrassChartOneDef),
				By(
					subfield,
					algebraic_element.PolynomialImageRing.Read(L).At(k, sm),
					fractional_ideal.SpanOneAndElement.Read(L).At(polynomialsS, um)))

			// The twisted generators of chart 1: the COND reads 0 at one and −2 at y, one ≠ y.
			nonzero := arg.Conjuncts(
				GroupPremises(datum, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")[0]
			onem := arg.MemberOf[on.L](arg.TermAs[A]("L.one"), comm_ring.OneIn.Read(ring))
			atOne := arg.Have(
				"the generator at one is x⁰ · one = one",
				"laurent_monomial(x, 0) * L.one = L.one",
				By(
					nonzero,
					laurent_polynomial.LaurentMonomialProduct.Read(L).At(xm),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(onem)))
			squared := arg.Have(
				"x⁻² is inv(x) squared",
				"laurent_monomial(x, -int_of_num(2)) = monoid_pow(L.mul, L.one, L.inv(x), 2)",
				By(laurent_polynomial.LaurentMonomialOfNum.At(
					arg.TermAs[Op[A]]("L.mul"),
					arg.TermAs[A]("L.one"),
					arg.TermAs[Fun[A, A]]("L.inv"),
					x,
					arg.TermAs[Nat]("2"))))
			atY := arg.Have(
				"so the generator at y is x⁻² · y = u",
				"laurent_monomial(x, -int_of_num(2)) * y = y * (L.inv(x) * L.inv(x))",
				squared.Rw(),
				ByArith(ring, ym, sm))
			generators := arg.Have(
				"the twisted generators are one and u",
				"{laurent_monomial(x, COND(e = L.one, int_of_num(0), -int_of_num(2))) * e | "+
					"    e:A | "+
					"    e ∈ {L.one, y}} = "+
					"{L.one, y * (L.inv(x) * L.inv(x))}",
				BySets(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b), atOne, atY))

			arg.Show(
				"unfolded, the free pair along (one, y) is the pair of these two spans, which are the two charts",
				Simp(
					Fwd(projective_line_free_pair.ProjectiveLineFreePairDef),
					Fwd(generators),
					Fwd(chart0),
					Fwd(chart1)),
				Refl())
		}),
})}

// GenusOne — the curve has genus one: H¹ of its structure pair is
// one-dimensional over k. Read over the line of x, the structure pair is
// the free pair O(0) · 1 ⊕ O(−2) · y, and H¹ is the same module over the
// line's overlap k[x, 1/x] as over the curve's, so the line's count along
// the independent {1, y} is the genus: max(−0 − 1, 0) + max(2 − 1, 0) = 1.
var GenusOne = genusOneThm{family.Add(registry.ProofEntry{
	Name: "GenusOne",
	Key:  "prop_52ce00884160be26",
	Reading: "Along the basis 1, y the structure pair is O(0) ⊕ O(−2) " +
		"on the line (StructurePairFree), and h¹(O(0)) + h¹(O(−2)) = 0 + 1.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "curve_genus(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)) = " +
			"1",
		Abbrev: Abbrev{
			{Name: "genusOneStructurePair", Text: "(«curveChart0», «curveChart1»)"},
			{Name: "genusOneLineRing", Text: "restrict_ring(field_ring(L), «curveLaurent»)"},
			{Name: "genusOneField", Text: "regular_module(field_ring(L))"},
			{Name: "genusOneTwist", Text: "λe:A. COND(e = L.one, int_of_num(0), -int_of_num(2))"},
			{Name: "genusOneFreePair", Text: "projective_line_free_pair(L, k, x, {L.one, y}, «genusOneTwist»)"},
			{Name: "genusOneSummand", Text: "λe:A. " +
				"    int_max(-COND(e = L.one, int_of_num(0), -int_of_num(2)) - &1, &0)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], h Fact) {
			subfield, transcendental := WeierstrassSubfield.Read(h), WeierstrassTranscendental.Read(h)
			xm := arg.MemberOf[on.L](x, WeierstrassXInField.Read(h).AsFact())
			chart0, chart1, overlap :=
				arg.TermAs[Set[A]]("«curveChart0»"),
				arg.TermAs[Set[A]]("«curveChart1»"),
				arg.TermAs[Set[A]]("«curveOverlap»")
			structurePair := arg.TermAs[Prod[Set[A], Set[A]]]("«genusOneStructurePair»")
			polynomials := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveKx»)")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«genusOneField»")
			one, single, basisSet :=
				arg.TermAs[A]("L.one"), arg.TermAs[Set[A]]("{y}"), arg.TermAs[Set[A]]("{L.one, y}")
			twists := arg.TermAs[Fun[A, Int]]("«genusOneTwist»")

			// H¹ of the curve is H¹ of the free pair along {1, y} on the line.
			onLine := arg.Have(
				"H¹ of the structure pair is one module over the line's overlap k[x, 1/x] and over the curve's",
				"lattice_pair_h1(«genusOneLineRing», «genusOneField», «genusOneStructurePair») = "+
					"lattice_pair_h1(«curveOverlapRing», «genusOneField», «genusOneStructurePair»)",
				By(
					h,
					WeierstrassIsCurve.Read(L).At(k, x, y, a, b),
					algebraic_curve.CurveLatticeData.Read(L).At(k, chart0, chart1, overlap, x),
					algebraic_curve.CurvePairOnLine.Read(L).At(k, chart0, chart1, overlap, x, structurePair)))
			// The free pair is the structure pair read back (StructurePairFree), its H¹ over the line's ring is
			// its H¹ over the curve's (onLine), and the two dimensions' scalars, the ring on k under L's
			// operations, are one term once restrict_ring is unfolded.
			genusOnLine := arg.Have(
				"so the genus is h¹ of the free pair O(0) · 1 ⊕ "+
					"O(−2) · y on the line, both dimensions taken over k",
				"curve_genus(field_ring(L), k, «curveChart0», «curveChart1», «curveOverlap») = "+
					"lattice_pair_h1_dim(«genusOneLineRing», k, «genusOneField», «genusOneFreePair»)",
				Simp(Fwd(algebraic_curve.CurveGenusDef), Fwd(lattice_pair.LatticePairH1DimDef)),
				GroupPremises(h, StructurePairFree.Read(L).At(k, x, y, a, b)).RwRev(),
				onLine.Rw(),
				Unfold(module_record.RestrictRingDef))

			// The line's count along {1, y}.
			basis := arg.Conjuncts(
				GroupPremises(h, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"chart 0 holds k[x]",
				"{one, y} is a basis of chart 0 over k[x]",
				"one is not y")
			basisOneY, oneNotY := basis[2], basis[3]
			independent := arg.Have(
				"{one, y} is independent over k[x], inside L as inside chart 0",
				"module_independent(restrict_ring(field_ring(L), «curveKx»), «genusOneField», {L.one, y})",
				By(
					comm_ring.SubringSubset.Read(basis[0]),
					arg.Unfolded(basisOneY, linear_independence.ModuleBasisDef),
					linear_independence.IndependentRestrict.At(polynomials, vectors, chart0, basisSet)))
			count := arg.Have(
				"along the finite independent {one, y}, h¹ of the free pair is the sum of max(−N(e) − 1, 0)",
				"int_of_num(lattice_pair_h1_dim(«genusOneLineRing», k, «genusOneField», «genusOneFreePair»)) = "+
					"int_sum({L.one, y}, «genusOneSummand»)",
				By(
					subfield,
					transcendental,
					finite_set.FiniteInsert.At(one, single),
					finite_set.FiniteSing.At(y),
					independent,
					projective_line_free_pair.FreeLinePairH1Dim.Read(L).At(k, xm, basisSet, twists)))

			// The sum: one turn of the recursion at the new point one, then the single point y.
			oneOutside := arg.Have(
				"one, not being y, does not lie in {y}",
				"L.one ∉ {y}",
				BySets(oneNotY))
			twist := arg.Have(
				"the twist at y is −2, y not being one",
				"COND(y = L.one, int_of_num(0), -int_of_num(2)) = -int_of_num(2)",
				By(oneNotY))
			sum := arg.Have(
				"so the sum is max(−0 − 1, 0) + max(2 − 1, 0) = 1",
				"int_sum({L.one, y}, «genusOneSummand») = &1",
				Simp(
					Fwd(int_sum.IntSumDef),
					Fwd(monoidal.OneTurn.Read(int_real_lift.MonoidalAdd)),
					Fwd(monoidal.Sing.Read(int_real_lift.MonoidalAdd)),
					Fwd(finite_set.FiniteSing),
					Fwd(oneOutside)),
				ByArith(twist))
			arg.Show(
				"the genus is that count, one",
				By(genusOnLine, count, sum, int_embed.OfNumEq))
		}),
})}

// EulerStructureZero — the structure pair of the curve has finite
// cohomology and Euler characteristic zero.
var EulerStructureZero = eulerStructureZeroThm{family.Add(registry.ProofEntry{
	Name: "EulerStructureZero",
	Key:  "prop_daf39d8dbc5569cc",
	Reading: "χ(O) = h⁰ − h¹ = 1 − 1: h⁰ = 1, the constants " +
		"(WeierstrassGlobalSections), and h¹ = 1, the genus (GenusOne).",
	Deps: []registry.EntryLike{
		GenusOne,
		WeierstrassIsCurve,
		algebraic_curve.StructureEuler,
		algebraic_curve.StructureFinite,
		lattice_pair.LatticePairEulerDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "lattice_pair_finite(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))) ∧ " +
			"lattice_pair_euler(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))) = " +
			"&0",
	},
		"the datum is a curve (WeierstrassIsCurve), so StructureFinite gives "+
			"finiteness and StructureEuler gives χ(O) = 1 − g, with g = 1 by GenusOne"),
})}
