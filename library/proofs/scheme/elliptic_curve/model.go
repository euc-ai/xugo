// model.go — the two affine rings of the curve y² = x³ + ax + b as
// quotients of free algebras over k: the Weierstrass ring k[x, y]/(y² −
// x³ − ax − b) and the ring of the chart at the origin, k[s, u]/(u² − s −
// as³ − bs⁴), where s = 1/x and u = y/x². Each is a domain; in a powerset
// host each has room for its cotangent complex; over a field where 2 ≠ 0
// and 4a³ + 27b² ≠ 0 the two partial derivatives of each relation
// generate the unit ideal, and read as elements of the function field they
// span each chart inside it; so each module of Kähler differentials is free
// on one invariant differential and each ring is smooth over k, every
// higher André–Quillen cohomology vanishing.

package elliptic_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/kaehler"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// The free algebra over k on the names x and y and the relation; the
// same on the names s and u for the chart at the origin.
const (
	weierAlgebra       = "universe_algebra_ring(k, {x, y})"
	weierRelation      = "weierstrass_relation(k, x, y, a, b)"
	weierChartAlgebra  = "universe_algebra_ring(k, {s, u})"
	weierChartRelation = "weierstrass_chart_one_relation(k, s, u, a, b)"
)

// weierVar and weierConst are the variable of a name and the constant of
// a scalar in the free algebras over k.
func weierVar(v string) string   { return "universe_algebra_var(k, " + v + ")" }
func weierConst(c string) string { return "universe_algebra_const(k, " + c + ")" }

func weierSub(alg, p, q string) string { return alg + ".sub(" + p + ", " + q + ")" }
func weierMul(alg, p, q string) string { return alg + ".mul(" + p + ", " + q + ")" }

// ---------------------------------------------------------------------------
// The two rings
// ---------------------------------------------------------------------------

// weierstrassRelationDef — `weierstrass_relation(k, x, y, a, b)`: the
// member y² − x³ − ax − b of the free algebra over k on the names x and
// y.
var weierstrassRelationDef = weierstrassRelationDefThm{family.Define(registry.DefEntry{
	Name:  "weierstrassRelationDef",
	Key:   "prop_26e9b535d4865cca",
	Const: "weierstrass_relation",
	Type:  "ring_ops(A) → U → U → A → A → U",
	Equations: []string{
		"∀k:ring_ops(A). ∀x y:U. ∀a b:A. weierstrass_relation(k, x, y, a, b) = " +
			weierSub(weierAlgebra, weierSub(weierAlgebra, weierSub(weierAlgebra,
				weierMul(weierAlgebra, weierVar("y"), weierVar("y")),
				weierMul(weierAlgebra, weierVar("x"), weierMul(weierAlgebra, weierVar("x"), weierVar("x")))),
				weierMul(weierAlgebra, weierConst("a"), weierVar("x"))),
				weierConst("b")),
	},
	Reading: "A member of the free algebra on {x, y} once a and b lie in k's carrier, read as a " +
		"polynomial under cotangent_universe(k, 𝕌⟨A:U⟩), which makes the universe embedding of k an " +
		"embedding. It is monic of degree two in y, the cubic x³ + ax + b its constant term over k[x].",
})}

// WeierstrassRingDef — `weierstrass_ring(k, x, y, a, b)`: the ring
// k[x, y]/(y² − x³ − ax − b), the cosets of the ideal the relation
// generates in the free algebra on x and y.
var WeierstrassRingDef = weierstrassRingDefThm{family.Define(registry.DefEntry{
	Name:  "WeierstrassRingDef",
	Key:   "prop_4e3c709c595d8ccf",
	Const: "weierstrass_ring",
	Type:  "ring_ops(A) → U → U → A → A → ring_ops(set(U))",
	Equations: []string{
		"∀k:ring_ops(A). ∀x y:U. ∀a b:A. weierstrass_ring(k, x, y, a, b) = koszul_quotient(" + weierAlgebra + ", " + weierRelation + ")",
	},
	Reading: "The affine ring of the curve y² = x³ + ax + b away from its point at infinity. x " +
		"and y are two names of the host, the variables of the free algebra; at x = y the record is " +
		"the one-variable ring k[y]/(y² − y³ − ay − b), so the statements that read the curve ask x " +
		"≠ y. The class of a polynomial p is koszul_projection(universe_algebra_ring(k, {x, y}), " +
		"weierstrass_relation(k, x, y, a, b), p), and k maps in through the classes of the constants.",
	Deps: []registry.EntryLike{weierstrassRelationDef},
})}

// weierstrassChartOneRelationDef — `weierstrass_chart_one_relation(k, s,
// u, a, b)`: the member u² − s − as³ − bs⁴ of the free algebra over k on
// the names s and u.
var weierstrassChartOneRelationDef = weierstrassChartOneRelationDefThm{family.Define(registry.DefEntry{
	Name:  "weierstrassChartOneRelationDef",
	Key:   "prop_345c56cbdc0384ad",
	Const: "weierstrass_chart_one_relation",
	Type:  "ring_ops(A) → U → U → A → A → U",
	Equations: []string{
		"∀k:ring_ops(A). ∀s u:U. ∀a b:A. weierstrass_chart_one_relation(k, s, u, a, b) = " +
			weierSub(weierChartAlgebra, weierSub(weierChartAlgebra, weierSub(weierChartAlgebra,
				weierMul(weierChartAlgebra, weierVar("u"), weierVar("u")),
				weierVar("s")),
				weierMul(
					weierChartAlgebra,
					weierConst("a"),
					weierMul(
						weierChartAlgebra, weierVar("s"), weierMul(weierChartAlgebra, weierVar("s"), weierVar("s"))))),
				weierMul(
					weierChartAlgebra,
					weierConst("b"),
					weierMul(
						weierChartAlgebra,
						weierVar("s"),
						weierMul(
							weierChartAlgebra, weierVar("s"), weierMul(weierChartAlgebra, weierVar("s"), weierVar("s")))))),
	},
	Reading: "The relation y² = x³ + ax + b divided by x⁴ and written in s " +
		"= 1/x and u = y/x²: u² = s + as³ + bs⁴. It is monic of degree two in u, " +
		"and its constant term over k[s], s(1 + as² + bs³), has order one at s = 0.",
})}

// weierstrassChartOneRingDef — `weierstrass_chart_one_ring(k, s, u, a,
// b)`: the ring k[s, u]/(u² − s − as³ − bs⁴) of the chart at the origin
// of the curve.
var weierstrassChartOneRingDef = weierstrassChartOneRingDefThm{family.Define(registry.DefEntry{
	Name:  "weierstrassChartOneRingDef",
	Key:   "prop_d86f4f3e4ee5f8d1",
	Const: "weierstrass_chart_one_ring",
	Type:  "ring_ops(A) → U → U → A → A → ring_ops(set(U))",
	Equations: []string{
		"∀k:ring_ops(A). ∀s u:U. ∀a b:A. weierstrass_chart_one_ring(k, s, u, a, b) = koszul_quotient(" + weierChartAlgebra + ", " + weierChartRelation + ")",
	},
	Reading: "The affine ring of the curve near its point at infinity, the origin s = " +
		"u = 0 of this chart; where x ≠ 0 the two charts glue by s = 1/x, u = y/x². s and u " +
		"are two names of the host and may be the names x and y themselves, each ring being " +
		"a quotient of its own free algebra; the statements that read the chart ask s ≠ u.",
	Deps: []registry.EntryLike{weierstrassChartOneRelationDef},
})}

// WeierstrassRingDomain — both rings are integral domains: y² − x³ − ax
// − b and u² − s − as³ − bs⁴ are irreducible.
var WeierstrassRingDomain = weierstrassRingDomainThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassRingDomain",
	Key:  "prop_3f0594e4f5faf092",
	Reading: "No characteristic and no discriminant hypothesis, and k need only be a domain (a " +
		"field is one, FieldIntegralDomain): y² − (x³ + ax + b) is irreducible because a square in " +
		"k[x] has even degree and x³ + ax + b odd, and u² − (s + as³ + bs⁴) because a square has " +
		"even order at s = 0 and s + as³ + bs⁴ order one. So the cusp y² = x³ (a = b = 0) is a " +
		"domain too. x ≠ y is load-bearing: at x = y and a = b = 0 the ring is k[y]/(y²(1 − y)). a " +
		"and b in k's carrier keep the relations in the free algebras; off it the constant of a is " +
		"the embedding at a function that is no polynomial, nothing is said of it. Characteristic " +
		"2 is included. s ≠ u is load-bearing on the chart-one ring as x ≠ y is on the first.",
	Deps: []registry.EntryLike{
		WeierstrassRingDef,
		weierstrassRelationDef,
		weierstrassChartOneRingDef,
		weierstrassChartOneRelationDef,
		integral_domain.IntegralDomainOn,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraDisjointCoefficients,
		free_algebra.PolynomialOneVariableHomomorphism,
		free_algebra.PolynomialOneVariableInjective,
		free_algebra.PolynomialOneVariableOnto,
		polynomial.DegreeMul,
		polynomial.PolynomialDomain,
		cotangent_examples.KoszulQuotientIdealQuotient,
		quotient_ring.QuotientRingOn,
		quotient_ring.CosetEqIff,
	},
	Build: family.Card(Statement{
		Binders: "∀k:ring_ops(A). ∀x y s u:U. ∀a b:A.",
		Hypotheses: []string{
			"cotangent_universe(k, 𝕌⟨A:U⟩)",
			"integral_domain_on(k)",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"x ≠ y",
			"s ≠ u",
		},
		Conclusion: "integral_domain_on(weierstrass_ring(k, x, y, a, b)) ∧ " +
			"integral_domain_on(weierstrass_chart_one_ring(k, s, u, a, b))",
	},
		"every member of the Weierstrass ring is the class of p₀ + p₁·y with p₀, p₁ in the algebra on "+
			"{x}: expand in powers of y over that algebra (FreeAlgebraDisjointCoefficients) and replace y² "+
			"by x³ + ax + b, the pair unique since the relation is monic of degree two in y. The norm N(p₀ "+
			"+ p₁y) = p₀² − p₁²(x³ + ax + b) is multiplicative and zero only at p₀ = p₁ = 0, since through "+
			"the one-variable bridge (PolynomialOneVariableHomomorphism, PolynomialOneVariableInjective, "+
			"PolynomialOneVariableOnto) degrees add over the domain k (DegreeMul, PolynomialDomain) and "+
			"p₀² has even degree, p₁²(x³ + ax + b) odd; a zero product has a zero norm, hence a zero "+
			"factor, and one ≠ zero since the relation is no unit. The chart-one ring the same with u over "+
			"the algebra on {s}, the order at s = 0 in place of the degree"),
})}

// WeierstrassRingInUniverse — in the powerset host the two rings have
// room for their cotangent complexes.
var WeierstrassRingInUniverse = weierstrassRingInUniverseThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassRingInUniverse",
	Key:  "prop_9d94ba3cdf098aa7",
	Reading: "No hypothesis, not even that k is a ring: the free algebra on two names is a ring on " +
		"the host's own subsets, which has room there (FreeAlgebraCotangentUniverse), and a quotient's " +
		"carrier is an image of its carrier (QuotientCotangentUniverse). The rings live on " +
		"set(set(prod(num, D))), a type the host does not fit; the room is their carriers'. With k's " +
		"room in the host (PowerSetUniverse) the tower k → k[x, y] → weierstrass_ring has a universe " +
		"for each of its rings, the hypothesis the cotangent complexes of the two charts are read under.",
	Deps: []registry.EntryLike{
		WeierstrassRingDef,
		weierstrassChartOneRingDef,
		cotangent_examples.KoszulQuotientIdealQuotient,
		simplicial_ring.FreeAlgebraCotangentUniverse,
		simplicial_ring.QuotientCotangentUniverse,
	},
	Build: family.Card(Statement{
		Binders: "∀k:ring_ops(A). ∀x y s u:set(prod(num, D)). ∀a b:A.",
		Conclusion: "cotangent_universe(«weierRing», 𝕌⟨A:set(prod(num, D))⟩) ∧ " +
			"cotangent_universe(«weierChartRing», 𝕌⟨A:set(prod(num, D))⟩)",
		Abbrev: Abbrev{
			{Name: "weierRing", Text: "weierstrass_ring(k, x, y, a, b)"},
			{Name: "weierChartRing", Text: "weierstrass_chart_one_ring(k, s, u, a, b)"},
		},
	},
		"unfold each ring (WeierstrassRingDef, weierstrassChartOneRingDef) to koszul_quotient "+
			"of a free algebra, which is ideal_quotient_ring at the ideal the relation spans "+
			"(KoszulQuotientIdealQuotient); the free algebra has a universe in the host "+
			"(FreeAlgebraCotangentUniverse), and so has its quotient (QuotientCotangentUniverse)"),
})}

// ---------------------------------------------------------------------------
// Smoothness
// ---------------------------------------------------------------------------

// WeierstrassPartialsUnit — over a field where 2 ≠ 0 and 4a³ + 27b² ≠ 0,
// the two partial derivatives of each relation generate the unit ideal
// of its ring: (2y, 3x² + a) = (1) and (2u, 1 + 3as² + 4bs³) = (1).
var WeierstrassPartialsUnit = weierstrassPartialsUnitThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassPartialsUnit",
	Key:  "prop_f330b206cdac77ef",
	Reading: "The partials are ∂_x = −(3x² + a), ∂_y = 2y and ∂_s = −(1 + 3as² + 4bs³), ∂_u = " +
		"2u, so the statement is (2y, 3x² + a) = (1) and (2u, 1 + 3as² + 4bs³) = (1): the Jacobian " +
		"criterion, which makes both charts smooth (WeierstrassChartsSmooth). 2 ≠ 0 is " +
		"load-bearing — in characteristic 2 the first ideal is (x² + a), a proper one — and so is " +
		"4a³ + 27b² ≠ 0, the resultant of x³ + ax + b and its derivative: at a = b = 0 both " +
		"partials lie in the ideal of the cusp x = y = 0. Characteristic 3 is allowed: there 4a³ + " +
		"27b² is a³ and 3x² + a is the unit a. The chart-one relation is u² − s·(1 + as² + bs³), " +
		"and s·(1 + as² + bs³) is s⁴ times x³ + ax + b at x = 1/s, so a common root of it and its " +
		"derivative would be 1/r for a double root r of the cubic. The cofactor identities of both " +
		"charts hold over ℤ, which is why characteristic 3 needs no separate argument.",
	Deps: []registry.EntryLike{
		WeierstrassRingDef,
		weierstrassRelationDef,
		weierstrassChartOneRingDef,
		weierstrassChartOneRelationDef,
		field.RingSubfieldDef,
		field.FieldOn,
		simplicial_ring.UniverseEmbeddingHost,
		partial_derivative.PartialVar,
		partial_derivative.PartialConst,
		partial_derivative.PartialAdd,
		partial_derivative.PartialLeibniz,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
		cotangent_examples.KoszulQuotientIdealQuotient,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.CosetEqIff,
	},
	Build: family.Card(Statement{
		Binders: "∀k:ring_ops(A). ∀inv:(A → A). ∀x y s u:U. ∀a b:A.",
		Hypotheses: []string{
			"cotangent_universe(k, 𝕌⟨A:U⟩)",
			"ring_subfield(k, inv, k.carrier)",
			"k.add(k.one, k.one) ≠ k.zero",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"k.add(k.mul(monoid_pow(k.add, k.zero, k.one, 4), k.mul(a, k.mul(a, a))), " +
				"    k.mul(monoid_pow(k.add, k.zero, k.one, 27), k.mul(b, b))) ≠ " +
				"k.zero",
			"x ≠ y",
			"s ≠ u",
		},
		Conclusion: "(∃α β:set(U). " +
			"    α ∈ weierstrass_ring(k, x, y, a, b).carrier ∧ " +
			"    β ∈ weierstrass_ring(k, x, y, a, b).carrier ∧ " +
			"    weierstrass_ring(k, x, y, a, b).add(weierstrass_ring(k, x, y, a, b).mul(α, " +
			"            koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                weierstrass_relation(k, x, y, a, b), " +
			"                free_algebra_partial(universe_embedding(k), " +
			"                    k, " +
			"                    x, " +
			"                    weierstrass_relation(k, x, y, a, b)))), " +
			"        weierstrass_ring(k, x, y, a, b).mul(β, " +
			"            koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                weierstrass_relation(k, x, y, a, b), " +
			"                free_algebra_partial(universe_embedding(k), " +
			"                    k, " +
			"                    y, " +
			"                    weierstrass_relation(k, x, y, a, b))))) = " +
			"    weierstrass_ring(k, x, y, a, b).one) ∧ " +
			"(∃α β:set(U). " +
			"    α ∈ weierstrass_chart_one_ring(k, s, u, a, b).carrier ∧ " +
			"    β ∈ weierstrass_chart_one_ring(k, s, u, a, b).carrier ∧ " +
			"    weierstrass_chart_one_ring(k, s, u, a, b).add(weierstrass_chart_one_ring(k, " +
			"            s, " +
			"            u, " +
			"            a, " +
			"            b).mul(α, " +
			"            koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                free_algebra_partial(universe_embedding(k), " +
			"                    k, " +
			"                    s, " +
			"                    weierstrass_chart_one_relation(k, s, u, a, b)))), " +
			"        weierstrass_chart_one_ring(k, s, u, a, b).mul(β, " +
			"            koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                free_algebra_partial(universe_embedding(k), " +
			"                    k, " +
			"                    u, " +
			"                    weierstrass_chart_one_relation(k, s, u, a, b))))) = " +
			"    weierstrass_chart_one_ring(k, s, u, a, b).one)",
	},
		"compute the partials (PartialVar, PartialConst, PartialAdd, PartialLeibniz). With g = x³ + "+
			"ax + b and Δ = 4a³ + 27b², (27b − 18a·x)·g + (6a·x² − 9b·x + 4a²)·g′ = Δ in the free algebra "+
			"(FreeAlgebraCommRingOn), and y² = g in the quotient (IdealQuotientProjection through "+
			"KoszulQuotientIdealQuotient), so α = −(6ax² − 9bx + 4a²)/Δ and β = (27b − 18ax)·y/(2Δ) are "+
			"cofactors, 2 and Δ invertible in the field (FieldOn). On the chart-one ring, with g₁ = s + "+
			"as³ + bs⁴ = u², p·g₁ + q·g₁′ = Δ for p = −a²b − (18a⁴ + 120ab²)·s − 24b(a³ + 6b²)·s² and q = "+
			"Δ + a²b·s + 3a(2a³ + 13b²)·s² + 6b(a³ + 6b²)·s³, which gives α = −q/Δ and β = p·u/(2Δ)"),
})}

// WeierstrassChartPartialsUnit — inside L, the ideal of chart 0 spanned by
// 2y and 3x² + a is chart 0, and the ideal of chart 1 spanned by 2u and
// 1 + 3as² + 4bs³ is chart 1, for s = 1/x and u = y/x². Both charts are one
// argument: in a subring C of L holding k, members w, d, p and q with
// p·w² + q·d = Δ = 4a³ + 27b² give the cofactors α = p·w/(2Δ) and β = q/Δ,
// which lie in C since ½ and 1/Δ lie in k, with α·2w + β·d = one; and a pair
// with a combination equal to one spans the ring (ring_ideal.SpanPairWhole).
// On chart 0, w = y and d = g₀′ for g₀ = x³ + ax + b = y², and p₀ = 27b − 18ax
// and q₀ = 6ax² − 9bx + 4a² satisfy p₀·g₀ + q₀·g₀′ = Δ in every commutative
// ring. On chart 1, w = u and d = g₁′ for g₁ = s + as³ + bs⁴ = u², and the
// cofactors p₁, q₁ of p₁·g₁ + q₁·g₁′ = Δ are the p₁ of degree at most two and
// q₁ of degree at most three that solve the linear system the identity is,
// polynomials in s whose coefficients c₁, …, c₄ lie in k. One ByArith checks
// each identity.
var WeierstrassChartPartialsUnit = weierstrassChartPartialsUnitThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartPartialsUnit",
	Key:  "prop_4041659d1729a27e",
	Reading: "The two generators are the partials ∂_y and −∂_x of y² − x³ − ax − b, and ∂_u and " +
		"−∂_s of u² − s − as³ − bs⁴, read as elements of L. 2 ≠ 0 is load-bearing: in characteristic " +
		"2 the first ideal is (x² + a), proper. So is 4a³ + 27b² ≠ 0: at a = b = 0 both generators " +
		"lie in the ideal of the cusp. Characteristic 3 is allowed, the discriminant there being a³. " +
		"Neither finite(k) nor any property of k beyond being a subfield holding a and b is used.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "ideal_span(restrict_ring(field_ring(L), «curveChart0»), " +
			"    {y + y, monoid_pow(L.add, L.zero, L.one, 3) * (x * x) + a}) = " +
			"«curveChart0» ∧ " +
			"ideal_span(restrict_ring(field_ring(L), «curveChart1»), " +
			"    {«curveU» + «curveU», " +
			"        L.one + " +
			"        monoid_pow(L.add, L.zero, L.one, 3) * (a * «curveS2») + " +
			"        monoid_pow(L.add, L.zero, L.one, 4) * (b * (L.inv(x) * «curveS2»))}) = " +
			"«curveChart1»",
		Abbrev: Abbrev{
			{Name: "numeral", Text: "λn:num. monoid_pow(L.add, L.zero, L.one, n)"},
			{Name: "Δ", Text: "«numeral»(4) * (a * (a * a)) + «numeral»(27) * (b * b)"},
			{Name: "g₀′", Text: "«numeral»(3) * (x * x) + a"},
			{Name: "p₀", Text: "«numeral»(27) * b - «numeral»(18) * (a * x)"},
			{Name: "q₀", Text: "«numeral»(6) * (a * (x * x)) - " +
				"«numeral»(9) * (b * x) + " +
				"«numeral»(4) * (a * a)"},
			{Name: "g₁′", Text: "L.one + " +
				"«numeral»(3) * (a * «curveS2») + " +
				"«numeral»(4) * (b * (L.inv(x) * «curveS2»))"},
			{Name: "c₁", Text: "a * (a * b)"},
			{Name: "c₂", Text: "«numeral»(18) * (a * (a * (a * a))) + «numeral»(120) * (a * (b * b))"},
			{Name: "c₃", Text: "«numeral»(3) * (a * («numeral»(2) * (a * (a * a)) + «numeral»(13) * (b * b)))"},
			{Name: "c₄", Text: "«numeral»(6) * (b * (a * (a * a) + «numeral»(6) * (b * b)))"},
			{Name: "p₁", Text: "-«c₁» - «c₂» * L.inv(x) - «numeral»(4) * «c₄» * «curveS2»"},
			{Name: "q₁", Text: "«Δ» + «c₁» * L.inv(x) + «c₃» * «curveS2» + «c₄» * (L.inv(x) * «curveS2»)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], smooth Fact) {
			clauses := arg.Conjuncts(
				arg.Simplified(smooth, Fwd(SmoothWeierstrassDef)),
				"a Weierstrass datum",
				"over a field where 2 ≠ 0",
				"with 4a³ + 27b² ≠ 0")
			datum, twoNonzero, discriminantNonzero := clauses[0], clauses[1], clauses[2]
			kSubfield, aInK, bInK :=
				WeierstrassSubfield.Read(datum),
				WeierstrassCoefficientA.Read(datum),
				WeierstrassCoefficientB.Read(datum)
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			sm := arg.MemberOf[on.L](arg.TermAs[A]("L.inv(x)"), GroupPremises(xm, field.InvIn.Read(L).At(xm)))
			ring := field.RingOn.Read(L)

			// ½ and 1/Δ: k is a field holding one, a and b.
			constantsRing := arg.Have(
				"k, a subfield of L, is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), k))",
				By(kSubfield, field.SubfieldCommRing.Read(L).At(k)))
			constants := arg.Have(
				"k holds Δ and 2, so their inverses ½ and 1/Δ",
				"L.inv(L.one + L.one) ∈ k ∧ L.inv(«Δ») ∈ k",
				By(
					kSubfield,
					aInK,
					bInK,
					field.SubfieldInv,
					comm_ring.AddIn.Read(constantsRing),
					comm_ring.MulIn.Read(constantsRing),
					comm_ring.OneIn.Read(constantsRing),
					comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(constantsRing))))
			coefficients := arg.Have(
				"a and b lie in L, as k does",
				"a ∈ L.carrier ∧ b ∈ L.carrier",
				BySets(kSubfield, field.SubfieldSubset, aInK, bInK))
			inverses := arg.Conjuncts(
				arg.Have(
					"2 and Δ are not zero, so ½ and 1/Δ invert them",
					"L.inv(L.one + L.one) * (L.one + L.one) = L.one ∧ L.inv(«Δ») * «Δ» = L.one",
					By(
						twoNonzero,
						discriminantNonzero,
						coefficients,
						field.MulLeftInverseOn.Read(L),
						comm_ring.AddIn.Read(ring),
						comm_ring.MulIn.Read(ring),
						comm_ring.OneIn.Read(ring),
						comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)))),
				"½ · 2 = one",
				"1/Δ · Δ = one")
			half, inverseDiscriminant := inverses[0], inverses[1]

			spanning := arg.Have(
				"in a subring C of L holding k, members w, d, p and q with p · w² + q · d = Δ make 2w and d span C",
				Statement{
					Binders: "∀C:set(A). ∀w d p q:A.",
					Hypotheses: []string{
						"subring(field_ring(L), C)",
						"k ⊆ C",
						"w ∈ C",
						"d ∈ C",
						"p ∈ C",
						"q ∈ C",
						"p * (w * w) + q * d = «Δ»",
					},
					Conclusion: "ideal_span(restrict_ring(field_ring(L), C), {w + w, d}) = C",
				},
				Derive(func(c *Argument) {
					C := c.FixAs[Set[A]]("C")
					c.Fix("w")
					d := c.FixAs[A]("d")
					c.Fix("p")
					c.Fix("q")
					given := c.Conjuncts(
						c.Assume(),
						"C is a subring of L",
						"holding k",
						"w lies in C",
						"so does d",
						"and p",
						"and q",
						"p · w² + q · d = Δ")
					subringC, identity := given[0], given[6]
					chartRing := c.Have(
						"C, a subring of L, is a ring",
						"comm_ring_on(restrict_ring(field_ring(L), C))",
						By(subringC, comm_ring.SubringRingOn.Read(ring).At(C)))
					inverseIn := c.Have(
						"½ and 1/Δ lie in C, as k does",
						"L.inv(L.one + L.one) ∈ C ∧ L.inv(«Δ») ∈ C",
						BySets(given[1], constants))
					members := c.Have(
						"so do 2w and the cofactors p · w / (2Δ) and q / Δ",
						"w + w ∈ C ∧ L.inv(«Δ») * (L.inv(L.one + L.one) * (p * w)) ∈ C ∧ L.inv(«Δ») * q ∈ C",
						By(
							given[2],
							given[4],
							given[5],
							inverseIn,
							comm_ring.AddIn.Read(chartRing),
							comm_ring.MulIn.Read(chartRing)))
					inL := c.Have(
						"w, d, p and q lie in L, as C does",
						"w ∈ L.carrier ∧ d ∈ L.carrier ∧ p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(given[2], given[3], given[4], given[5], comm_ring.SubringSubset.Read(subringC)))
					combination := c.Have(
						"the cofactors α = p · w / (2Δ) and β = q / Δ give α · 2w + β · d = (p · w² + q · d) / Δ = one",
						"L.inv(«Δ») * (L.inv(L.one + L.one) * (p * w)) * (w + w) + L.inv(«Δ») * q * d = L.one",
						ByArith(
							ring,
							inL,
							coefficients,
							Scaled(c.TermAs[A]("L.inv(«Δ») * (p * (w * w))"), half),
							Scaled(c.TermAs[A]("L.inv(«Δ»)"), identity),
							inverseDiscriminant))
					c.Show(
						"so 2w and d span C",
						By(
							chartRing,
							members,
							given[3],
							combination,
							Read(ring_ideal.SpanPairWhole, chartRing).At(
								c.TermAs[A]("w + w"),
								d,
								c.TermAs[A]("L.inv(«Δ») * (L.inv(L.one + L.one) * (p * w))"),
								c.TermAs[A]("L.inv(«Δ») * q"))))
				}))

			arg.Show(
				"on each chart the two partials and the cofactors "+
					"of the identity lie in the chart, so they span it",
				SplitConj(
					Case(
						"chart 0: p₀ · y² + q₀ · g₀′ = Δ, since p₀ · g₀ + q₀ · g₀′ = Δ and y² = g₀",
						Derive(func(c *Argument) {
							chart := c.Conjuncts(
								GroupPremises(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
								"chart 0 is a subring of L",
								"holding k[x]",
								"free over k[x] on one and y",
								"one is not y")
							line := c.Conjuncts(
								GroupPremises(kSubfield, algebraic_element.PolynomialImageRing.Read(L).At(k, xm)),
								"k[x] is a subring of L",
								"holding k",
								"and x",
								"inside k(x)")
							yIn := c.Have(
								"y = 0 + 1 · y lies in chart 0",
								"y ∈ «curveChart0»",
								Simp(Fwd(WeierstrassChartZeroMembers)),
								Witness(c.TermAs[A]("L.zero")),
								Witness(c.TermAs[A]("L.one")),
								ByArith(ring, ym, comm_ring.SubringZero.Read(line[0]), comm_ring.SubringOne.Read(line[0])))
							atoms := c.Have(
								"k and x lie in chart 0, through k[x], and with k so do a and b",
								"k ⊆ «curveChart0» ∧ x ∈ «curveChart0» ∧ a ∈ «curveChart0» ∧ b ∈ «curveChart0»",
								BySets(chart[1], line[1], line[2], aInK, bInK))
							chartRing := c.Have(
								"chart 0, a subring of L, is a ring",
								"comm_ring_on(restrict_ring(field_ring(L), «curveChart0»))",
								By(chart[0], comm_ring.SubringRingOn.Read(ring).At(c.TermAs[Set[A]]("«curveChart0»"))))
							polynomials := c.Have(
								"p₀, q₀ and g₀′ = 3x² + a, polynomials in x over k, lie in chart 0",
								"«p₀» ∈ «curveChart0» ∧ «q₀» ∈ «curveChart0» ∧ «g₀′» ∈ «curveChart0»",
								By(
									atoms,
									comm_ring.AddIn.Read(chartRing),
									comm_ring.SubIn.Read(chartRing),
									comm_ring.MulIn.Read(chartRing),
									comm_ring.OneIn.Read(chartRing),
									comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(chartRing))))
							relation := c.Simplified(WeierstrassEquation.Read(datum).AsFact())
							identity := c.Have(
								"p₀ · y² + q₀ · g₀′ = p₀ · g₀ + q₀ · g₀′ = Δ, as y² = g₀ = x³ + ax + b",
								"«p₀» * (y * y) + «q₀» * «g₀′» = «Δ»",
								ByArith(ring, xm, ym, coefficients, Scaled(c.TermAs[A]("«p₀»"), relation)))
							c.Show(
								"so the span of 2y and g₀′ is chart 0",
								By(
									chart[0],
									atoms,
									yIn,
									polynomials,
									identity,
									spanning.At(
										c.TermAs[Set[A]]("«curveChart0»"),
										y,
										c.TermAs[A]("«g₀′»"),
										c.TermAs[A]("«p₀»"),
										c.TermAs[A]("«q₀»"))))
						})),
					Case(
						"chart 1: p₁ · u² + q₁ · g₁′ = Δ, since p₁ · g₁ + q₁ · g₁′ = Δ and u² = g₁",
						Derive(func(c *Argument) {
							chart := c.Conjuncts(
								GroupPremises(datum, WeierstrassBasisOne.Read(L).At(k, x, y, a, b)),
								"chart 1 is a subring of L",
								"holding k[s]",
								"free over k[s] on one and u",
								"one is not u")
							line := c.Conjuncts(
								GroupPremises(kSubfield, algebraic_element.PolynomialImageRing.Read(L).At(k, sm)),
								"k[s] is a subring of L",
								"holding k",
								"and s",
								"inside k(s)")
							uIn := c.Have(
								"u = 0 + 1 · u lies in chart 1",
								"«curveU» ∈ «curveChart1»",
								Simp(Fwd(WeierstrassChartOneMembers)),
								Witness(c.TermAs[A]("L.zero")),
								Witness(c.TermAs[A]("L.one")),
								ByArith(ring, ym, sm, comm_ring.SubringZero.Read(line[0]), comm_ring.SubringOne.Read(line[0])))
							atoms := c.Have(
								"k and s lie in chart 1, through k[s], and with k so do a and b",
								"k ⊆ «curveChart1» ∧ L.inv(x) ∈ «curveChart1» ∧ a ∈ «curveChart1» ∧ b ∈ «curveChart1»",
								BySets(chart[1], line[1], line[2], aInK, bInK))
							chartRing := c.Have(
								"chart 1, a subring of L, is a ring",
								"comm_ring_on(restrict_ring(field_ring(L), «curveChart1»))",
								By(chart[0], comm_ring.SubringRingOn.Read(ring).At(c.TermAs[Set[A]]("«curveChart1»"))))
							// The coefficients first, then p₁, q₁ and g₁′ over them: each closure close stays one level deep.
							coefficientsIn := c.Have(
								"Δ and the coefficients c₁, c₂, c₃, c₄ of p₁ and q₁ lie in chart 1, as a and b do",
								"«Δ» ∈ «curveChart1» ∧ "+
									"«c₁» ∈ «curveChart1» ∧ "+
									"«c₂» ∈ «curveChart1» ∧ "+
									"«c₃» ∈ «curveChart1» ∧ "+
									"«c₄» ∈ «curveChart1»",
								By(
									atoms,
									comm_ring.AddIn.Read(chartRing),
									comm_ring.MulIn.Read(chartRing),
									comm_ring.OneIn.Read(chartRing),
									comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(chartRing))))
							polynomials := c.Have(
								"so do p₁, q₁ and g₁′ = 1 + 3as² + 4bs³, polynomials in s",
								"«p₁» ∈ «curveChart1» ∧ «q₁» ∈ «curveChart1» ∧ «g₁′» ∈ «curveChart1»",
								By(
									atoms,
									coefficientsIn,
									comm_ring.AddIn.Read(chartRing),
									comm_ring.SubIn.Read(chartRing),
									comm_ring.NegIn.Read(chartRing),
									comm_ring.MulIn.Read(chartRing),
									comm_ring.OneIn.Read(chartRing),
									comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(chartRing))))
							relation := c.Simplified(
								GroupPremises(datum, WeierstrassChartOneEquation.Read(L).At(k, x, y, a, b)))
							identity := c.Have(
								"p₁ · u² + q₁ · g₁′ = p₁ · g₁ + q₁ · g₁′ = Δ, as u² = g₁ = s + as³ + bs⁴",
								"«p₁» * («curveU» * «curveU») + «q₁» * «g₁′» = «Δ»",
								ByArith(ring, ym, sm, coefficients, Scaled(c.TermAs[A]("«p₁»"), relation)))
							c.Show(
								"so the span of 2u and g₁′ is chart 1",
								By(
									chart[0],
									atoms,
									uIn,
									polynomials,
									identity,
									spanning.At(
										c.TermAs[Set[A]]("«curveChart1»"),
										c.TermAs[A]("«curveU»"),
										c.TermAs[A]("«g₁′»"),
										c.TermAs[A]("«p₁»"),
										c.TermAs[A]("«q₁»"))))
						})),
				))
		}),
})}

// WeierstrassKaehlerAffine — over a field where 2 ≠ 0 and 4a³ + 27b² ≠
// 0, the module of Kähler differentials of each ring over k is free of
// rank one on an invariant differential ω, with dx = 2y·ω and dy =
// (3x² + a)·ω on the Weierstrass chart, ds = 2u·ω and du = (1 + 3as² +
// 4bs³)·ω on the chart at the origin.
var WeierstrassKaehlerAffine = weierstrassKaehlerAffineThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassKaehlerAffine",
	Key:  "prop_e2fc938e3998ea8b",
	Reading: "ω is the invariant differential dx/2y = dy/(3x² + a), defined on the whole chart " +
		"because 2y and 3x² + a generate the unit ideal (WeierstrassPartialsUnit); on the chart at the " +
		"origin it is ds/2u, and where the charts meet, s = 1/x and u = y/x², ds/2u = −dx/2y. The " +
		"isomorphism is r ↦ r•ω from the ring as a module over itself. Without 4a³ + 27b² ≠ 0 the module " +
		"is not free: on the cusp a = b = 0 it needs both dx and dy at x = y = 0, two generators there. " +
		"The two equations fix ω: it is β·dx − α·dy for the cofactors α, β of WeierstrassPartialsUnit.",
	Deps: []registry.EntryLike{
		WeierstrassPartialsUnit,
		kaehler.KaehlerUniversalExists,
		kaehler.KaehlerUniversalUnique,
		kaehler.KaehlerSpan,
		kaehler.UniversalDerivationIsDerivation,
		kaehler.KaehlerModuleOn,
		partial_derivative.FreeAlgebraDerivationFromValues,
		partial_derivative.DerivationUniqueOnGenerators,
		partial_derivative.DerivationOn,
		partial_derivative.PartialVar,
		partial_derivative.PartialConst,
		partial_derivative.PartialAdd,
		partial_derivative.PartialLeibniz,
		quotient_ring.IdealQuotientProjection,
		cotangent_examples.KoszulQuotientIdealQuotient,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀k:ring_ops(A). ∀inv:(A → A). ∀x y s u:U. ∀a b:A.",
		Hypotheses: []string{
			"cotangent_universe(k, 𝕌⟨A:U⟩)",
			"ring_subfield(k, inv, k.carrier)",
			"k.add(k.one, k.one) ≠ k.zero",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"k.add(k.mul(monoid_pow(k.add, k.zero, k.one, 4), k.mul(a, k.mul(a, a))), " +
				"    k.mul(monoid_pow(k.add, k.zero, k.one, 27), k.mul(b, b))) ≠ " +
				"k.zero",
			"x ≠ y",
			"s ≠ u",
		},
		Conclusion: "(∃ω:set(set(U) → set(U)). " +
			"    module_isomorphism(weierstrass_ring(k, x, y, a, b), " +
			"        mk_module(weierstrass_ring(k, x, y, a, b).add, " +
			"            weierstrass_ring(k, x, y, a, b).zero, " +
			"            weierstrass_ring(k, x, y, a, b).neg, " +
			"            weierstrass_ring(k, x, y, a, b).mul, " +
			"            weierstrass_ring(k, x, y, a, b).carrier), " +
			"        kaehler_module(k, " +
			"            weierstrass_ring(k, x, y, a, b), " +
			"            λc:A. " +
			"                koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                    weierstrass_relation(k, x, y, a, b), " +
			"                    universe_algebra_const(k, c))), " +
			"        λr:set(U). " +
			"            kaehler_module(k, " +
			"                weierstrass_ring(k, x, y, a, b), " +
			"                λc:A. " +
			"                    koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                        weierstrass_relation(k, x, y, a, b), " +
			"                        universe_algebra_const(k, c))).smul(r, ω)) ∧ " +
			"    universal_derivation(k, " +
			"        weierstrass_ring(k, x, y, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                weierstrass_relation(k, x, y, a, b), " +
			"                universe_algebra_const(k, c)), " +
			"        koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"            weierstrass_relation(k, x, y, a, b), " +
			"            universe_algebra_var(k, x))) = " +
			"    kaehler_module(k, " +
			"        weierstrass_ring(k, x, y, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                weierstrass_relation(k, x, y, a, b), " +
			"                universe_algebra_const(k, c))).smul(koszul_projection( " +
			"            universe_algebra_ring(k, {x, y}), " +
			"            weierstrass_relation(k, x, y, a, b), " +
			"            universe_algebra_ring(k, {x, y}).add(universe_algebra_var(k, y), " +
			"                universe_algebra_var(k, y))), " +
			"        ω) ∧ " +
			"    universal_derivation(k, " +
			"        weierstrass_ring(k, x, y, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                weierstrass_relation(k, x, y, a, b), " +
			"                universe_algebra_const(k, c)), " +
			"        koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"            weierstrass_relation(k, x, y, a, b), " +
			"            universe_algebra_var(k, y))) = " +
			"    kaehler_module(k, " +
			"        weierstrass_ring(k, x, y, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                weierstrass_relation(k, x, y, a, b), " +
			"                universe_algebra_const(k, c))).smul(koszul_projection( " +
			"            universe_algebra_ring(k, {x, y}), " +
			"            weierstrass_relation(k, x, y, a, b), " +
			"            universe_algebra_ring(k, {x, y}).add(universe_algebra_ring(k, {x, y}).mul( " +
			"                    universe_algebra_const(k, monoid_pow(k.add, k.zero, k.one, 3)), " +
			"                    universe_algebra_ring(k, {x, y}).mul(universe_algebra_var(k, x), " +
			"                        universe_algebra_var(k, x))), " +
			"                universe_algebra_const(k, a))), " +
			"        ω)) ∧ " +
			"(∃ω:set(set(U) → set(U)). " +
			"    module_isomorphism(weierstrass_chart_one_ring(k, s, u, a, b), " +
			"        mk_module(weierstrass_chart_one_ring(k, s, u, a, b).add, " +
			"            weierstrass_chart_one_ring(k, s, u, a, b).zero, " +
			"            weierstrass_chart_one_ring(k, s, u, a, b).neg, " +
			"            weierstrass_chart_one_ring(k, s, u, a, b).mul, " +
			"            weierstrass_chart_one_ring(k, s, u, a, b).carrier), " +
			"        kaehler_module(k, " +
			"            weierstrass_chart_one_ring(k, s, u, a, b), " +
			"            λc:A. " +
			"                koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                    weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                    universe_algebra_const(k, c))), " +
			"        λr:set(U). " +
			"            kaehler_module(k, " +
			"                weierstrass_chart_one_ring(k, s, u, a, b), " +
			"                λc:A. " +
			"                    koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                        weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                        universe_algebra_const(k, c))).smul(r, ω)) ∧ " +
			"    universal_derivation(k, " +
			"        weierstrass_chart_one_ring(k, s, u, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                universe_algebra_const(k, c)), " +
			"        koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"            weierstrass_chart_one_relation(k, s, u, a, b), " +
			"            universe_algebra_var(k, s))) = " +
			"    kaehler_module(k, " +
			"        weierstrass_chart_one_ring(k, s, u, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                universe_algebra_const(k, c))).smul(koszul_projection( " +
			"            universe_algebra_ring(k, {s, u}), " +
			"            weierstrass_chart_one_relation(k, s, u, a, b), " +
			"            universe_algebra_ring(k, {s, u}).add(universe_algebra_var(k, u), " +
			"                universe_algebra_var(k, u))), " +
			"        ω) ∧ " +
			"    universal_derivation(k, " +
			"        weierstrass_chart_one_ring(k, s, u, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                universe_algebra_const(k, c)), " +
			"        koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"            weierstrass_chart_one_relation(k, s, u, a, b), " +
			"            universe_algebra_var(k, u))) = " +
			"    kaehler_module(k, " +
			"        weierstrass_chart_one_ring(k, s, u, a, b), " +
			"        λc:A. " +
			"            koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                universe_algebra_const(k, c))).smul(koszul_projection( " +
			"            universe_algebra_ring(k, {s, u}), " +
			"            weierstrass_chart_one_relation(k, s, u, a, b), " +
			"            universe_algebra_ring(k, {s, u}).add(universe_algebra_ring(k, {s, u}).add( " +
			"                    universe_algebra_ring(k, {s, u}).one, " +
			"                    universe_algebra_ring(k, {s, u}).mul(universe_algebra_const(k, " +
			"                            k.mul(monoid_pow(k.add, k.zero, k.one, 3), a)), " +
			"                        universe_algebra_ring(k, {s, u}).mul(universe_algebra_var(k, s), " +
			"                            universe_algebra_var(k, s)))), " +
			"                universe_algebra_ring(k, {s, u}).mul( " +
			"                    universe_algebra_const(k, k.mul(monoid_pow(k.add, k.zero, k.one, 4), b)), " +
			"                    universe_algebra_ring(k, {s, u}).mul(universe_algebra_var(k, s), " +
			"                        universe_algebra_ring(k, {s, u}).mul(universe_algebra_var(k, s), " +
			"                            universe_algebra_var(k, s)))))), " +
			"        ω))",
	},
		"the values 2ȳ at x and 3x̄² + a at y give a derivation of the free algebra along the "+
			"projection (FreeAlgebraDerivationFromValues), zero at the relation, where its value is "+
			"−(3x̄² + a)·2ȳ + 2ȳ·(3x̄² + a), hence on the ideal the relation spans by Leibniz; it "+
			"descends to a derivation δ of the quotient over k, and KaehlerUniversalExists gives h "+
			"with h(dz) = δ(z). With α, β from WeierstrassPartialsUnit put ω = β·dx̄ − α·dȳ: h(ω) = 1, "+
			"and dx̄ − 2ȳ·ω and dȳ − (3x̄² + a)·ω are α and β times d of the relation's class, zero, d "+
			"of a class being Σ_v ∂_v·dv̄ (a derivation of the free algebra fixed by its values at the "+
			"variables, DerivationUniqueOnGenerators). So every dz is a multiple of ω, r ↦ r•ω is onto "+
			"(KaehlerSpan), and h after it is the identity; the same on the chart-one ring"),
})}

// WeierstrassChartsSmooth — over a field where 2 ≠ 0 and 4a³ + 27b² ≠ 0,
// both rings are smooth over k: Dⁿ(A/k, N) = 0 for every n ≥ 1 and every
// module N, so D¹ and D² vanish.
var WeierstrassChartsSmooth = weierstrassChartsSmoothThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartsSmooth",
	Key:  "prop_d5c341b3b78d83b6",
	Reading: "D² = 0 says every deformation of a chart is unobstructed, D¹ = 0 that it is unique up " +
		"to isomorphism, for every coefficient module. The host is the subsets of prod(num, D), chosen " +
		"from k alone: the free algebras and the two rings have room there whenever k does " +
		"(PowerSetUniverse, FreeAlgebraCotangentUniverse, WeierstrassRingInUniverse). The hypotheses are " +
		"WeierstrassPartialsUnit's and load-bearing as there: at a = b = 0 the cusp's chart has D¹(A/k, " +
		"A/(x̄, ȳ)) = A/(x̄, ȳ), both partials acting as zero. Dⁿ for n ≥ 2 vanishes on any plane curve " +
		"with a regular equation (PlaneCurveCohomologyVanishes); only D¹ reads the discriminant.",
	Deps: []registry.EntryLike{
		cotangent_examples.PlaneCurveCohomologyLowDegrees,
		cotangent_examples.PlaneCurveCohomologyVanishes,
		WeierstrassPartialsUnit,
		WeierstrassRingInUniverse,
		simplicial_ring.PowerSetUniverse,
		simplicial_ring.FreeAlgebraCotangentUniverse,
		field.RingSubfieldDef,
		field.FieldOn,
		free_algebra.FreeAlgebraDisjointCoefficients,
		free_algebra.FreeAlgebraCommRingOn,
		cotangent_complex.CotangentCohomologyModuleOn,
		module_homomorphism.ModuleIsomorphismDef,
		WeierstrassRingDef,
		weierstrassChartOneRingDef,
		weierstrassRelationDef,
		weierstrassChartOneRelationDef,
	},
	Build: family.Card(Statement{
		Binders: "∀k:ring_ops(A). ∀inv:(A → A). ∀x y s u:set(prod(num, D)). ∀a b:A.",
		Hypotheses: []string{
			"card_le(k.carrier, 𝕌⟨A:set(prod(num, D))⟩)",
			"ring_subfield(k, inv, k.carrier)",
			"k.add(k.one, k.one) ≠ k.zero",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"k.add(k.mul(monoid_pow(k.add, k.zero, k.one, 4), k.mul(a, k.mul(a, a))), " +
				"    k.mul(monoid_pow(k.add, k.zero, k.one, 27), k.mul(b, b))) ≠ " +
				"k.zero",
			"x ≠ y",
			"s ≠ u",
		},
		Conclusion: "(∀N:module_ops(set(set(prod(num, D))), E). " +
			"    module_on(weierstrass_ring(k, x, y, a, b), N) ⇒ " +
			"    ∀n:num. " +
			"        1 ≤ n ⇒ " +
			"        cotangent_cohomology⟨U:set(prod(num, D))⟩(k, " +
			"            weierstrass_ring(k, x, y, a, b), " +
			"            λc:A. " +
			"                koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                    weierstrass_relation(k, x, y, a, b), " +
			"                    universe_algebra_const(k, c)), " +
			"            weierstrass_ring(k, x, y, a, b), " +
			"            λz:set(set(prod(num, D))). z, " +
			"            N, " +
			"            n).carrier = " +
			"        {cotangent_cohomology(k, " +
			"                weierstrass_ring(k, x, y, a, b), " +
			"                λc:A. " +
			"                    koszul_projection(universe_algebra_ring(k, {x, y}), " +
			"                        weierstrass_relation(k, x, y, a, b), " +
			"                        universe_algebra_const(k, c)), " +
			"                weierstrass_ring(k, x, y, a, b), " +
			"                λz:set(set(prod(num, D))). z, " +
			"                N, " +
			"                n).zero}) ∧ " +
			"(∀N:module_ops(set(set(prod(num, D))), E). " +
			"    module_on(weierstrass_chart_one_ring(k, s, u, a, b), N) ⇒ " +
			"    ∀n:num. " +
			"        1 ≤ n ⇒ " +
			"        cotangent_cohomology⟨U:set(prod(num, D))⟩(k, " +
			"            weierstrass_chart_one_ring(k, s, u, a, b), " +
			"            λc:A. " +
			"                koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                    weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                    universe_algebra_const(k, c)), " +
			"            weierstrass_chart_one_ring(k, s, u, a, b), " +
			"            λz:set(set(prod(num, D))). z, " +
			"            N, " +
			"            n).carrier = " +
			"        {cotangent_cohomology(k, " +
			"                weierstrass_chart_one_ring(k, s, u, a, b), " +
			"                λc:A. " +
			"                    koszul_projection(universe_algebra_ring(k, {s, u}), " +
			"                        weierstrass_chart_one_relation(k, s, u, a, b), " +
			"                        universe_algebra_const(k, c)), " +
			"                weierstrass_chart_one_ring(k, s, u, a, b), " +
			"                λz:set(set(prod(num, D))). z, " +
			"                N, " +
			"                n).zero})",
	},
		"the relation is no zero divisor in the free algebra, monic of degree two in y over "+
			"the algebra on {x}: the top coefficient in y of a product with it is the other "+
			"factor's (FreeAlgebraDisjointCoefficients). The host has room for k, the free "+
			"algebra and the ring (PowerSetUniverse, FreeAlgebraCotangentUniverse, "+
			"WeierstrassRingInUniverse), so PlaneCurveCohomologyLowDegrees makes D¹(A/k, N) the "+
			"quotient of N by F_x·N + F_y·N, which is all of N since m = F_x·(α•m) + F_y·(β•m) "+
			"for the α, β of WeierstrassPartialsUnit, and a module isomorphic to a one-point "+
			"module is one point (ModuleIsomorphismDef); PlaneCurveCohomologyVanishes gives n ≥ "+
			"2. The same on the chart-one ring, its relation monic of degree two in u"),
})}
