// hypersurface.go — the ring side of the étale hypersurfaces: the
// quotient R[x]/(g) of the one-variable polynomials over a ring by the
// ideal one polynomial generates, its projection and its constants; a
// ring map from R[x] killing g factors through it, and g is separable
// exactly when its derivative is a unit in it. Two instances follow: the
// simple algebraic extension K(a) is the quotient of K[x] by the minimal
// polynomial of a, and the localization of R at the powers of f is the
// quotient of R[x] by f·x − 1.

package cotangent_examples

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The quotient R[x]/(g)
// ---------------------------------------------------------------------------

// hypersurfaceIdealDef — `hypersurface_ideal(R, g)`: the ideal g
// generates among the polynomials over the ring R, (g) on paper.
var hypersurfaceIdealDef = hypersurfaceIdealDefThm{family.Define(registry.DefEntry{
	Name:  "hypersurfaceIdealDef",
	Key:   "prop_7a048402c6b3a7e2",
	Const: "hypersurface_ideal",
	Type:  "ring_ops(A) → (num → A) → set(num → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:(num → A). hypersurface_ideal(R, g) = ideal_span(polynomial_ring(R), {g})",
	},
	Reading: "The span is the meet of the ideals of the polynomials over R holding g. When g is " +
		"no polynomial over R no such ideal exists, the meet of no sets is the whole type, and nothing " +
		"about it is a ring fact: every statement over it asks polynomial_over(R.zero, R.carrier, g).",
})}

// HypersurfaceRingDef — `hypersurface_ring(R, g)`: the ring R[x]/(g) as
// one record — the cosets of the ideal (g) among the polynomials over R,
// added, negated, multiplied and subtracted as the cosets of an ideal
// are, the ideal itself the zero and the coset of the one polynomial the
// one.
var HypersurfaceRingDef = hypersurfaceRingDefThm{family.Define(registry.DefEntry{
	Name:  "HypersurfaceRingDef",
	Key:   "prop_2329cc422f9e35e4",
	Const: "hypersurface_ring",
	Type:  "ring_ops(A) → (num → A) → ring_ops(set(num → A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:(num → A). " +
			"    hypersurface_ring(R, g) = " +
			"    mk_ring(set_mul(vec_add(R.add)), " +
			"        hypersurface_ideal(R, g), " +
			"        set_inv(vec_neg(R.neg)), " +
			"        quotient_mul(vec_add(R.add), " +
			"            polynomial_mul(R.add, R.zero, R.mul), " +
			"            hypersurface_ideal(R, g)), " +
			"        left_coset(vec_add(R.add), basis_vector(R.zero, R.one, 0), hypersurface_ideal(R, g)), " +
			"        quotient_sub(vec_add(R.add), vec_neg(R.neg)), " +
			"        left_cosets(vec_add(R.add), " +
			"            {p:(num → A) | polynomial_over(R.zero, R.carrier, p)}, " +
			"            hypersurface_ideal(R, g)))",
	},
	Reading: "The record is ideal_quotient_ring at polynomial_ring(R), so the quotient ring " +
		"chapter's laws apply after unfolding. At g a unit of R[x] — in the zero ring, at g = −1, " +
		"at f·x − 1 with f nilpotent — the ideal is every polynomial and the record is the zero " +
		"ring on one coset; at g = 0 every coset is one polynomial and the ring is R[x] again.",
	Deps: []registry.EntryLike{hypersurfaceIdealDef},
})}

// hypersurfaceProjectionDef — `hypersurface_projection(R, g, p)`: the
// class p + (g) of a polynomial; `hypersurface_projection(R, g)` is the
// quotient map R[x] → R[x]/(g).
var hypersurfaceProjectionDef = hypersurfaceProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "hypersurfaceProjectionDef",
	Key:   "prop_833f49cc54e9b67d",
	Const: "hypersurface_projection",
	Type:  "ring_ops(A) → (num → A) → (num → A) → set(num → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀g p:(num → A). " +
			"    hypersurface_projection(R, g, p) = left_coset(vec_add(R.add), p, hypersurface_ideal(R, g))",
	},
	Deps: []registry.EntryLike{hypersurfaceIdealDef},
})}

// hypersurfaceConstantDef — `hypersurface_constant(R, g, a)`: the class
// of the constant polynomial a; `hypersurface_constant(R, g)` is the map
// R → R[x]/(g) that makes the quotient an R-algebra.
var hypersurfaceConstantDef = hypersurfaceConstantDefThm{family.Define(registry.DefEntry{
	Name:  "hypersurfaceConstantDef",
	Key:   "prop_c62658bd5dfe54f3",
	Const: "hypersurface_constant",
	Type:  "ring_ops(A) → (num → A) → A → set(num → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:(num → A). ∀a:A. " +
			"    hypersurface_constant(R, g, a) = " +
			"    hypersurface_projection(R, g, vec_scalar_mul(R.mul, a, basis_vector(R.zero, R.one, 0)))",
	},
	Deps: []registry.EntryLike{hypersurfaceProjectionDef},
})}

// ---------------------------------------------------------------------------
// The ring R[x]/(g), its projection and its constants
// ---------------------------------------------------------------------------

// HypersurfaceIdealDivides — the ideal (g) is the polynomials over R
// that g divides over R.
var HypersurfaceIdealDivides = hypersurfaceIdealDividesThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceIdealDivides",
	Key:  "prop_8d03074b49e13d0e",
	Reading: "polynomial_over(R.carrier, g) is load-bearing: for g off the " +
		"polynomials over R the ideal is the whole type (hypersurfaceIdealDef), which " +
		"the multiples of g need not be. The cofactor is over R, so every member of " +
		"the ideal is a polynomial over R; at g = vec_zero the ideal is {vec_zero}.",
	Deps: []registry.EntryLike{
		hypersurfaceIdealDef,
		polynomial_division.PolynomialDividesDef,
		polynomial.PolynomialRingOn,
		polynomial.BasisVectorOver,
		polynomial.BasisVectorMul,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanLeast,
		ring_ideal.SpanContains,
		ring_ideal.IdealMul,
		ring_ideal.RingIdealDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g p:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "p ∈ hypersurface_ideal(R, g) ⇔ polynomial_divides(R, g, p)",
	},
		"the multiples polynomial_mul(g, r), r over R, form an ideal of the polynomials over R — "+
			"closed under sums and under products by polynomials, commutativity moving the factor "+
			"(PolynomialRingOn) — holding g = polynomial_mul(g, basis_vector(0)) (BasisVectorOver, the "+
			"one law of PolynomialRingOn), so the span lies among them (SpanLeast); a multiple lies in "+
			"every ideal holding g (IdealMul, the product commuted), so in the span (IdealSpanDef)"),
})}

// HypersurfaceRingOn — R[x]/(g) is a commutative ring on its cosets.
var HypersurfaceRingOn = hypersurfaceRingOnThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceRingOn",
	Key:  "prop_f10830a1682cccd5",
	Reading: "The ring is the zero ring exactly when g is a unit of R[x]: in " +
		"the zero ring, at g a unit constant, at f·x − 1 with f nilpotent. At g " +
		"= vec_zero every coset is one polynomial and the ring is R[x] again.",
	Deps: []registry.EntryLike{
		HypersurfaceRingDef,
		hypersurfaceIdealDef,
		quotient_ring.QuotientRingOn,
		polynomial.PolynomialRingOn,
		ring_ideal.SpanIdeal,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "comm_ring_on(hypersurface_ring(R, g))",
	},
		"unfold hypersurface_ring: the record's operations are quotient_ring_ops at the polynomial "+
			"ring's operations polynomial_ops(R) and its carrier the cosets of (g) among the polynomials "+
			"over R, so the statement is quotient_ring.QuotientRingOn at the polynomial ring "+
			"(PolynomialRingOn) and the ideal the span is (SpanIdeal, g lying among the polynomials over R)"),
})}

// HypersurfaceProjectionHomomorphism — the projection is a ring
// homomorphism from the polynomials over R onto R[x]/(g).
var HypersurfaceProjectionHomomorphism = hypersurfaceProjectionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceProjectionHomomorphism",
	Key:  "prop_47e4e0ad7526863e",
	Reading: "The image clause makes every member of R[x]/(g) the class of a " +
		"polynomial over R; HypersurfaceInducedMap, SeparableIffDerivativeUnit " +
		"and FxMinusOneFractions pick their representatives through it.",
	Deps: []registry.EntryLike{
		HypersurfaceRingDef,
		hypersurfaceProjectionDef,
		hypersurfaceIdealDef,
		quotient_ring.ProjectionHomomorphism,
		polynomial.PolynomialRingOn,
		ring_ideal.SpanIdeal,
		quotient_group.LeftCosetsDef,
		set_basic.ImageDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "ring_homomorphism(polynomial_ring(R), " +
			"    hypersurface_ring(R, g), " +
			"    hypersurface_projection(R, g)) ∧ " +
			"image(hypersurface_projection(R, g), {p:num → A | polynomial_over(R.carrier, p)}) = " +
			"hypersurface_ring(R, g).carrier",
	},
		"unfold hypersurface_ring and hypersurface_projection: the map is p ↦ p + "+
			"(g), and the homomorphism is quotient_ring.ProjectionHomomorphism at the "+
			"polynomial ring (PolynomialRingOn) and the ideal (SpanIdeal); the cosets "+
			"are the image of the class map by their definition (LeftCosetsDef)"),
})}

// HypersurfaceClassEq — two polynomials over R have one class exactly
// when g divides their difference over R.
var HypersurfaceClassEq = hypersurfaceClassEqThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceClassEq",
	Key:  "prop_be093ef690dbdd79",
	Reading: "p and q are both asked to be over R: the equality of " +
		"classes is the coset law of the polynomial ring, read at members of " +
		"its carrier, and divisibility over R speaks of polynomials over R.",
	Deps: []registry.EntryLike{
		hypersurfaceProjectionDef,
		hypersurfaceIdealDef,
		HypersurfaceIdealDivides,
		quotient_ring.CosetEqIff,
		polynomial.PolynomialRingOn,
		ring_ideal.SpanIdeal,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g p q:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "hypersurface_projection(R, g, p) = hypersurface_projection(R, g, q) ⇔ " +
			"polynomial_divides(R, g, vec_sub(p, q))",
	},
		"quotient_ring.CosetEqIff at the polynomial ring (PolynomialRingOn) "+
			"and the ideal (SpanIdeal): the classes agree exactly when p - q "+
			"lies in (g), which is divisibility by HypersurfaceIdealDivides"),
})}

// HypersurfaceConstantHomomorphism — the constants make R[x]/(g) an
// R-algebra: a ↦ the class of the constant a is a ring homomorphism.
var HypersurfaceConstantHomomorphism = hypersurfaceConstantHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceConstantHomomorphism",
	Key:  "prop_e53d9bc9eeb20af0",
	Reading: "a · e_0 is a polynomial over R only for a in R's carrier, where the map is asked to be " +
		"a homomorphism. When g is a unit of R[x] the quotient is the zero ring and the map is constant.",
	Deps: []registry.EntryLike{
		hypersurfaceConstantDef,
		HypersurfaceProjectionHomomorphism,
		HypersurfaceRingOn,
		polynomial.BasisVectorOver,
		polynomial.BasisVectorMul,
		polynomial.PolynomialRingOn,
		vec_space.VecScalarMulDef,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "ring_homomorphism(R, hypersurface_ring(R, g), hypersurface_constant(R, g))",
	},
		"a ↦ a • basis_vector(0) carries R into the polynomials over R (BasisVectorOver, "+
			"the scaled coefficients in R's carrier) and keeps the sum (scaling distributes at "+
			"every index), the product ((a • basis_vector(0)) * (b • basis_vector(0)) = (a * b) "+
			"• basis_vector(0), BasisVectorMul with the scalars pulled out of the convolution) "+
			"and the one; composed with the projection (HypersurfaceProjectionHomomorphism) it "+
			"is the statement's map (hypersurfaceConstantDef), and a composite of homomorphisms "+
			"keeps each conjunct of ring_homomorphism, the target being HypersurfaceRingOn"),
})}

// HypersurfaceInducedMap — a ring homomorphism from the polynomials over
// R that kills g induces one from R[x]/(g), taking the class of p to the
// value at p.
var HypersurfaceInducedMap = hypersurfaceInducedMapThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceInducedMap",
	Key:  "prop_bf376d7e6fbb9b68",
	Reading: "φ(g) = T.zero is load-bearing: it makes φ constant on each class, so the " +
		"member induced_map chooses in a class gives the value at every representative. T is " +
		"any commutative ring on any type; both rings sit in φ's homomorphism fact. The induced " +
		"map is the only one with these values, every member of the carrier being a class.",
	Deps: []registry.EntryLike{
		equivalence.InducedMapDef,
		HypersurfaceIdealDivides,
		HypersurfaceProjectionHomomorphism,
		HypersurfaceRingOn,
		hypersurfaceProjectionDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		polynomial.PolynomialRingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:(num → A). ∀T:ring_ops(B). ∀φ:((num → A) → B).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"ring_homomorphism(polynomial_ring(R), T, φ)",
			"φ(g) = T.zero",
		},
		Conclusion: "ring_homomorphism(hypersurface_ring(R, g), T, induced_map(φ)) ∧ " +
			"(∀p:(num → A). " +
			"    polynomial_over(R.carrier, p) ⇒ induced_map(φ, hypersurface_projection(R, g, p)) = φ(p))",
	},
		"a member of the class of p is p + polynomial_mul(g, r) with r over R "+
			"(HypersurfaceIdealDivides), a polynomial over R, and φ sends it to φ(p) + φ(g) "+
			"* φ(r) = φ(p) (MapAdd, MapMul); the class holds p itself, zero lying in the "+
			"ideal, so the member induced_map chooses (InducedMapDef) has the value φ(p); "+
			"every member of the carrier is a class (HypersurfaceProjectionHomomorphism's "+
			"image clause), the operations of classes are the classes of the operations, and "+
			"the homomorphism laws are φ's at representatives (MapIn, MapAdd, MapMul, MapOne)"),
})}

// SeparableIffDerivativeUnit — a polynomial g over R is separable
// exactly when its derivative is a unit modulo g.
var SeparableIffDerivativeUnit = separableIffDerivativeUnitThm{family.Add(registry.ProofEntry{
	Name: "SeparableIffDerivativeUnit",
	Key:  "prop_243f0ea31badc210",
	Reading: "No field and no degree are asked: u * g + v * g' = 1 over R says " +
		"exactly that the class of g' is inverted by the class of v. In the zero " +
		"ring both sides hold; at g = vec_zero both say that R is the zero ring.",
	Deps: []registry.EntryLike{
		separable_polynomial.PolynomialSeparableDef,
		polynomial.DerivativeOver,
		ring_ideal.RingUnitDef,
		HypersurfaceProjectionHomomorphism,
		HypersurfaceClassEq,
		HypersurfaceRingOn,
		HypersurfaceRingDef,
		HypersurfaceIdealDivides,
		quotient_ring.CosetEqIdealIff,
		polynomial.PolynomialRingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "polynomial_separable(R, g) ⇔ " +
			"ring_unit(hypersurface_ring(R, g), hypersurface_projection(R, g, polynomial_derivative(g)))",
	},
		"⇒: the projection (HypersurfaceProjectionHomomorphism) sends the Bézout identity u * g + v * "+
			"g' = basis_vector(0) of polynomial_separable to class(u) * class(g) + class(v) * class(g') = "+
			"the one, and class(g) is the zero, g lying in its own ideal (HypersurfaceIdealDivides, "+
			"CosetEqIdealIff), so class(v) inverts class(g'), a class since g' is over R "+
			"(DerivativeOver); ⇐: the inverse is a class(v) with v over R, and class(g' * v) = "+
			"class(basis_vector(0)) gives g' * v - basis_vector(0) = polynomial_mul(g, w) with w over R "+
			"(HypersurfaceClassEq), so vec_neg(w) and v are a Bézout pair (the laws of PolynomialRingOn)"),
})}

// ---------------------------------------------------------------------------
// The simple algebraic extension K(a) is K[x]/(minimal polynomial)
// ---------------------------------------------------------------------------

// MinimalPolynomialRegular — the minimal polynomial is a
// non-zero-divisor among the polynomials over K.
var MinimalPolynomialRegular = minimalPolynomialRegularThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialRegular",
	Key:  "prop_c297de3d198048a7",
	Reading: "algebraic_over(K, a) is load-bearing: for a transcendental a the minimal " +
		"polynomial is chosen with nothing said of it, and may be vec_zero, which kills every q.",
	Deps: []registry.EntryLike{
		algebraic_element.MinimalPolynomialSpec,
		polynomial.PolynomialMonicDef,
		field.SubfieldFieldOn,
		field.OneNotZeroOn,
		integral_domain.FieldIntegralDomain,
		polynomial.PolynomialDomain,
		integral_domain.NoZeroDivisors,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀q:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
			"polynomial_over(K, q)",
			"polynomial_mul(minimal_polynomial(L, K, a), q) = vec_zero",
		},
		Conclusion: "q = vec_zero",
	},
		"the minimal polynomial is monic over K (MinimalPolynomialSpec), so not vec_zero, its "+
			"leading coefficient being one ≠ zero (PolynomialMonicDef, OneNotZeroOn); the polynomials "+
			"over the field on K (SubfieldFieldOn) form an integral domain (FieldIntegralDomain, "+
			"PolynomialDomain), so the other factor is vec_zero (NoZeroDivisors)"),
})}

// SeparableDerivativeUnit — when μ, the minimal polynomial of a over K,
// is separable, a is a simple root of it: the derivative μ' does not
// vanish at a, and μ'(a) is a unit of K(a). Evaluated at a, a Bézout
// identity u·μ + v·μ' = 1 over K leaves μ'(a)·v(a) = 1, since μ(a) = 0;
// v(a), a value of a polynomial over K, lies in K[a] ⊆ K(a). The identity
// is evaluated rather than separable_polynomial.SeparableRootSimple cited
// for μ'(a) ≠ 0 because it exhibits the inverse v(a) in K[a] at once.
var SeparableDerivativeUnit = separableDerivativeUnitThm{family.Add(registry.ProofEntry{
	Name: "SeparableDerivativeUnit",
	Key:  "prop_cecf0417476982c3",
	Reading: "Over a field of characteristic zero every minimal polynomial " +
		"is separable; the minimal polynomial x^p − t of a p-th root of t over " +
		"𝔽_p(t) has derivative zero, and the statement does not reach it.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
		},
		Conclusion: "polynomial_eval(«μ'», a) ≠ L.zero ∧ " +
			"ring_unit(restrict_ring(field_ring(L), field_adjoin(L, K, {a})), polynomial_eval(«μ'», a))",
		Abbrev: Abbrev{
			{Name: "μ'", Text: "polynomial_derivative(minimal_polynomial(L, K, a))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], a *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"K is a subfield of L",
				"a lies in L",
				"a is algebraic over K",
				"μ is separable over K")
			subK, algebraic, separable := hyp[0], hyp[2], hyp[3]
			aM := arg.MemberOf[on.L](a, hyp[1])
			ring := field.RingOn.Read(L)
			μ := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
			derivative := arg.TermAs[Fun[Nat, A]]("«μ'»")

			u, v, bezout := arg.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				arg.Unfolded(separable, separable_polynomial.PolynomialSeparableDef),
				"u",
				"v")
			coefficients := arg.Conjuncts(
				bezout,
				"u is a polynomial over K",
				"v is a polynomial over K",
				"u·μ + v·μ' is the one polynomial")
			uOverK, vOverK, identity := coefficients[0], coefficients[1], coefficients[2]
			spec := arg.Conjuncts(
				GroupPremises(subK, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, aM)),
				"μ is a polynomial over K",
				"μ is monic",
				"μ vanishes at a",
				"no nonzero polynomial over K vanishing at a has smaller degree")
			μOverK, root := spec[0], spec[2]

			derivativeOverK := arg.Have(
				"μ' is a polynomial over K, the derivative of one",
				"polynomial_over(K, «μ'»)",
				By(
					subK,
					μOverK,
					field.SubfieldSubring.Read(L).At(K),
					polynomial.DerivativeOver.Read(ring).At(K, μ)))
			zero, carrier := arg.TermAs[A]("L.zero"), arg.TermAs[Set[A]]("L.carrier")
			overL := arg.Have(
				"u, v, μ and μ' are polynomials over L, which holds K",
				"polynomial_over(L.carrier, u) ∧ "+
					"polynomial_over(L.carrier, v) ∧ "+
					"polynomial_over(L.carrier, minimal_polynomial(L, K, a)) ∧ "+
					"polynomial_over(L.carrier, «μ'»)",
				By(
					subK,
					uOverK,
					vOverK,
					μOverK,
					derivativeOverK,
					field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), K),
					polynomial.PolynomialOverMono.At(zero, K, carrier, u),
					polynomial.PolynomialOverMono.At(zero, K, carrier, v),
					polynomial.PolynomialOverMono.At(zero, K, carrier, μ),
					polynomial.PolynomialOverMono.At(zero, K, carrier, derivative)))

			value := arg.Have(
				"evaluated at a, the Bézout identity reads u(a)·μ(a) + v(a)·μ'(a) "+
					"= one, the one polynomial basis_vector(0) evaluating to a⁰ = one",
				"polynomial_eval(u, a) * polynomial_eval(minimal_polynomial(L, K, a), a) + "+
					"polynomial_eval(v, a) * polynomial_eval(«μ'», a) = "+
					"L.one",
				By(
					identity,
					overL,
					polynomial_evaluation.EvalAdd.Read(ring).At(
						arg.TermAs[Fun[Nat, A]]("polynomial_mul(u, minimal_polynomial(L, K, a))"),
						arg.TermAs[Fun[Nat, A]]("polynomial_mul(v, «μ'»)"),
						aM),
					polynomial_evaluation.EvalMul.Read(ring).At(u, μ, aM),
					polynomial_evaluation.EvalMul.Read(ring).At(v, derivative, aM),
					polynomial_evaluation.EvalBasisVector.Read(ring).At(arg.TermAs[Nat]("0"), aM),
					polynomial.PolynomialMulOver.Read(ring).At(u, μ),
					polynomial.PolynomialMulOver.Read(ring).At(v, derivative),
					comm_monoid.MonoidPowDef))
			inverse := arg.Have(
				"μ(a) = zero leaves μ'(a)·v(a) = one",
				"polynomial_eval(«μ'», a) * polynomial_eval(v, a) = L.one",
				ByArith(
					value,
					root,
					overL,
					polynomial_evaluation.EvalIn.Read(ring).At(u, aM),
					polynomial_evaluation.EvalIn.Read(ring).At(v, aM),
					polynomial_evaluation.EvalIn.Read(ring).At(derivative, aM)))
			inAdjoined := arg.Have(
				"μ' and v are polynomials over K, so μ'(a) and v(a) lie in K[a] ⊆ K(a)",
				"polynomial_eval(«μ'», a) ∈ field_adjoin(L, K, {a}) ∧ "+
					"polynomial_eval(v, a) ∈ field_adjoin(L, K, {a})",
				BySets(
					derivativeOverK,
					vOverK,
					subK,
					algebraic_element.PolynomialImageDef.At(arg.TermAs[RingOps[A]]("field_ring(L)"), K, a),
					algebraic_element.PolynomialImageRing.Read(L).At(K, aM)))
			arg.Show(
				"μ'(a) is nonzero and a unit of K(a), with inverse v(a)",
				SplitConj(
					Case(
						"μ'(a) = zero would make one = zero · v(a) = zero",
						By(
							field.OneNotZeroOn.Read(L),
							inverse,
							overL,
							polynomial_evaluation.EvalIn.Read(ring).At(v, aM),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(arg.TermAs[A]("polynomial_eval(v, a)")))),
					Case(
						"v(a) lies in K(a) and inverts μ'(a) there",
						By(
							inAdjoined,
							inverse,
							ring_ideal.RingUnitDef.At(
								arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), field_adjoin(L, K, {a}))"),
								arg.TermAs[A]("polynomial_eval(«μ'», a)"))))))
		}),
})}

// AdjoinEvaluationKernel — the polynomials over K vanishing at a are the
// ideal the minimal polynomial generates.
var AdjoinEvaluationKernel = adjoinEvaluationKernelThm{family.Add(registry.ProofEntry{
	Name: "AdjoinEvaluationKernel",
	Key:  "prop_87d5472d50d1143a",
	Reading: "The kernel is read on the polynomials over K, not over L: the " +
		"ideal the minimal polynomial generates holds polynomials over K alone, " +
		"while a polynomial over L vanishing at a has its cofactor over L only.",
	Deps: []registry.EntryLike{
		ring_homomorphism.RingKernelDef,
		set_basic.Extension,
		algebraic_element.MinimalPolynomialDivides,
		algebraic_element.MinimalPolynomialSpec,
		HypersurfaceIdealDivides,
		field.SubfieldFieldOn,
		polynomial_evaluation.EvalHomomorphism,
		polynomial.PolynomialOverMono,
		polynomial_division.PolynomialDividesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "ring_kernel(L.zero, " +
			"    {p:num → A | polynomial_over(K, p)}, " +
			"    λp:(num → A). polynomial_eval(p, a)) = " +
			"hypersurface_ideal(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
	},
		"extensionality (Extension, RingKernelDef): a polynomial over K vanishing at a is "+
			"divided over K by the minimal polynomial (MinimalPolynomialDivides), which is "+
			"membership in its ideal (HypersurfaceIdealDivides at the field on K, "+
			"SubfieldFieldOn, the minimal polynomial over K by MinimalPolynomialSpec); conversely "+
			"a member is polynomial_mul(μ, r) with r over K, a polynomial over K whose value at a "+
			"is μ(a) * r(a) = zero (EvalHomomorphism at the field on L, PolynomialOverMono)"),
})}

// AdjoinIsomorphicQuotient — K(a) is K[x] modulo the minimal polynomial
// of a: the map evaluation induces on the classes is an isomorphism of
// K-algebras.
var AdjoinIsomorphicQuotient = adjoinIsomorphicQuotientThm{family.Add(registry.ProofEntry{
	Name: "AdjoinIsomorphicQuotient",
	Key:  "prop_8ef22f44a40ae484",
	Reading: "induced_map evaluates a representative chosen in the class; every representative " +
		"has the same value at a, the minimal polynomial vanishing there. Algebraicity is " +
		"load-bearing: for a transcendental a the minimal polynomial is a sequence nothing is said " +
		"about, and K(a) holds quotients of polynomial values that no polynomial value reaches. " +
		"The last conjunct is the K-algebra condition, the class of the constant k going to k.",
	Deps: []registry.EntryLike{
		HypersurfaceInducedMap,
		algebraic_element.AdjoinEvaluationHomomorphism,
		AdjoinEvaluationKernel,
		HypersurfaceClassEq,
		HypersurfaceIdealDivides,
		hypersurfaceConstantDef,
		algebraic_element.MinimalPolynomialSpec,
		algebraic_element.AdjoinEqImage,
		algebraic_element.PolynomialImageDef,
		polynomial_evaluation.EvalScalar,
		polynomial_evaluation.EvalBasisVector,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingKernelDef,
		field.SubfieldFieldOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
		},
		Conclusion: "ring_isomorphism( " +
			"    hypersurface_ring(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a)), " +
			"    restrict_ring(field_ring(L), field_adjoin(L, K, {a})), " +
			"    induced_map(λp:(num → A). polynomial_eval(p, a))) ∧ " +
			"(∀k:A. " +
			"    k ∈ K ⇒ " +
			"    induced_map(λp:(num → A). polynomial_eval(p, a), " +
			"        hypersurface_constant(restrict_ring(field_ring(L), K), " +
			"            minimal_polynomial(L, K, a), " +
			"            k)) = " +
			"    k)",
	},
		"HypersurfaceInducedMap at the ring on K (SubfieldFieldOn) and evaluation at a "+
			"(AdjoinEvaluationHomomorphism, the minimal polynomial vanishing at a by "+
			"MinimalPolynomialSpec) makes induced_map(evaluation) a ring homomorphism sending the class "+
			"of p to p(a); it is injective on the classes — equal values make p - q vanish at a, so p - "+
			"q lies in the ideal (AdjoinEvaluationKernel, HypersurfaceIdealDivides) and the classes "+
			"agree (HypersurfaceClassEq) — and onto K(a) = K[a] (AdjoinEqImage, PolynomialImageDef); "+
			"the constant k • basis_vector(0) evaluates to k (EvalScalar, EvalBasisVector)"),
})}

// ---------------------------------------------------------------------------
// The localization at the powers of f is R[x]/(f·x − 1)
// ---------------------------------------------------------------------------

// FxMinusOneRegular — f·x − 1 is a polynomial over R and a
// non-zero-divisor among them.
var FxMinusOneRegular = fxMinusOneRegularThm{family.Add(registry.ProofEntry{
	Name: "FxMinusOneRegular",
	Key:  "prop_3ff22974f00b8136",
	Reading: "Only the constant term −1, a unit, is used: at f = zero the polynomial is " +
		"−1, and at f nilpotent it is a unit of R[x]; it is a non-zero-divisor in each case.",
	Deps: []registry.EntryLike{
		polynomial.PolynomialMulDef,
		polynomial.PolynomialOverDef,
		vec_space.VecSubDef,
		vec_space.VecScalarMulDef,
		vec_space.BasisVectorDef,
		vec_space.VecDef,
		comm_ring.MulIn,
		comm_ring.SubIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
		},
		Conclusion: "polynomial_over(R.carrier, " +
			"    vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))) ∧ " +
			"(∀q:(num → A). " +
			"    polynomial_over(R.carrier, q) ∧ " +
			"    polynomial_mul(vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), q) = " +
			"    vec_zero ⇒ " +
			"    q = vec_zero)",
	},
		"f • x - 1 is a 2-vector with the coefficients -one and f, in R's carrier "+
			"(VecSubDef, VecScalarMulDef, BasisVectorDef, VecDef); its product with q has the "+
			"coefficient -q(0) at 0 and f * q(n) - q(suc(n)) at suc(n) (PolynomialMulDef, the "+
			"sum over {i ≤ n} reduced to its two nonzero terms), so a zero product gives q(0) "+
			"= zero and q(suc(n)) = f * q(n), and q(n) = zero by induction on n"),
})}

// FxMinusOneSeparable — f·x − 1 is separable: its derivative is the
// constant f, and −1 · (f·x − 1) + x · f = 1.
var FxMinusOneSeparable = fxMinusOneSeparableThm{family.Add(registry.ProofEntry{
	Name: "FxMinusOneSeparable",
	Key:  "prop_76226f406e0e0852",
	Reading: "The derivative is the constant f, and the Bézout pair (−1, x) " +
		"works for every f: at f = 0 the polynomial is −1 and (−1) · (−1) = 1.",
	Deps: []registry.EntryLike{
		FxMinusOneRegular,
		separable_polynomial.PolynomialSeparableDef,
		polynomial.PolynomialDerivativeDef,
		polynomial.BasisVectorMul,
		polynomial.BasisVectorOver,
		polynomial.PolynomialRingOn,
		vec_space.VecScalarMulDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
		},
		Conclusion: "polynomial_separable(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)))",
	},
		"the derivative of f • x - 1 is f • basis_vector(0) (PolynomialDerivativeDef: "+
			"the coefficient at n is (n + 1) times the one at n + 1, which is f at 0 and "+
			"zero beyond); with u = vec_neg(basis_vector(0)) and v = basis_vector(1), both "+
			"over R (BasisVectorOver), u * (f • x - 1) + v * (f • basis_vector(0)) = (1 - f "+
			"• x) + f • x = basis_vector(0) (BasisVectorMul and the laws of PolynomialRingOn)"),
})}

// FxMinusOneInverts — modulo f·x − 1 the class of x inverts the
// constant f.
var FxMinusOneInverts = fxMinusOneInvertsThm{family.Add(registry.ProofEntry{
	Name: "FxMinusOneInverts",
	Key:  "prop_682fd0357575c60",
	Reading: "f · x − 1 lies in its own ideal, which is all the statement reads; for f " +
		"nilpotent or zero the quotient is the zero ring and the equation is one = one there.",
	Deps: []registry.EntryLike{
		hypersurfaceConstantDef,
		HypersurfaceProjectionHomomorphism,
		HypersurfaceClassEq,
		HypersurfaceRingDef,
		FxMinusOneRegular,
		polynomial.BasisVectorMul,
		polynomial.BasisVectorOver,
		polynomial_division.PolynomialDividesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
		},
		Conclusion: "hypersurface_ring(R, " +
			"    vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))).mul( " +
			"    hypersurface_constant(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), f), " +
			"    hypersurface_projection(R, " +
			"        vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), " +
			"        basis_vector(1))) = " +
			"hypersurface_ring(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))).one",
	},
		"the product of the classes is the class of (f • basis_vector(0)) * basis_vector(1) "+
			"= f • basis_vector(1) (HypersurfaceProjectionHomomorphism, BasisVectorMul); f • "+
			"basis_vector(1) - basis_vector(0) is f • x - 1 itself, divisible by itself with "+
			"cofactor basis_vector(0), so the class is that of the one polynomial "+
			"(HypersurfaceClassEq), which is the ring's one (HypersurfaceRingDef)"),
})}

// FxMinusOneFractions — modulo f·x − 1 every element times a power of f
// is a constant.
var FxMinusOneFractions = fxMinusOneFractionsThm{family.Add(registry.ProofEntry{
	Name: "FxMinusOneFractions",
	Key:  "prop_14abbc5390e2a2fa",
	Deps: []registry.EntryLike{
		HypersurfaceProjectionHomomorphism,
		HypersurfaceConstantHomomorphism,
		FxMinusOneInverts,
		FxMinusOneRegular,
		polynomial.PolynomialExpansion,
		polynomial.PolynomialOverDef,
		comm_monoid.PowAddOn,
		comm_monoid.MapPow,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A. ∀y:set(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
			"y ∈ hypersurface_ring(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))).carrier",
		},
		Conclusion: "∃a:A. ∃n:num. " +
			"    a ∈ R.carrier ∧ " +
			"    hypersurface_ring(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))).mul(y, " +
			"        hypersurface_constant(R, " +
			"            vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), " +
			"            monoid_pow(R.mul, R.one, f, n))) = " +
			"    hypersurface_constant(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), a)",
	},
		"y is the class of a polynomial p over R (HypersurfaceProjectionHomomorphism's image clause), an "+
			"n-vector (PolynomialOverDef), p = Σ_{i<n} p(i) • x ^ i (PolynomialExpansion); in the quotient "+
			"the class of x ^ i times the class of f ^ n is the class of f ^ (n - i) for i ≤ n, the class of "+
			"x inverting the class of f (FxMinusOneInverts, MapPow, PowAddOn), so y times the class of f ^ n "+
			"is the class of the constant Σ_{i<n} p(i) * f ^ (n - i) (HypersurfaceConstantHomomorphism)"),
})}

// FxMinusOneKernel — a constant that vanishes modulo f·x − 1 is killed
// by a power of f.
var FxMinusOneKernel = fxMinusOneKernelThm{family.Add(registry.ProofEntry{
	Name: "FxMinusOneKernel",
	Key:  "prop_43ad372efb08d686",
	Reading: "At f nilpotent every constant vanishes and is killed, " +
		"as the localization at the powers of f is then the zero ring.",
	Deps: []registry.EntryLike{
		HypersurfaceRingDef,
		hypersurfaceConstantDef,
		hypersurfaceProjectionDef,
		HypersurfaceIdealDivides,
		quotient_ring.CosetEqIdealIff,
		polynomial.PolynomialMulDef,
		polynomial.PolynomialOverDef,
		polynomial_division.PolynomialDividesDef,
		FxMinusOneRegular,
		comm_monoid.MonoidPowDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f a:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
			"a ∈ R.carrier",
			"hypersurface_constant(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), a) = " +
				"hypersurface_ring(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))).zero",
		},
		Conclusion: "∃n:num. R.mul(monoid_pow(R.mul, R.one, f, n), a) = R.zero",
	},
		"the ring's zero is the ideal (HypersurfaceRingDef), so a • "+
			"basis_vector(0) lies in it (CosetEqIdealIff) and is polynomial_mul(f • x "+
			"- 1, q) for a q over R (HypersurfaceIdealDivides); comparing coefficients "+
			"as in FxMinusOneRegular, q(0) = -a and q(suc(i)) = f * q(i), so q(i) = "+
			"-(f ^ i * a) by induction, and q being an n-vector gives f ^ n * a = zero"),
})}

// FxMinusOneIsLocalization — R[x]/(f·x − 1), with the constants, is a
// localization of R at the powers of f.
var FxMinusOneIsLocalization = fxMinusOneIsLocalizationThm{family.Add(registry.ProofEntry{
	Name: "FxMinusOneIsLocalization",
	Key:  "prop_111458037d3f0f51",
	Reading: "Every clause holds at f = 0, where the powers of f are {one, zero} and both " +
		"rings are the zero ring, and at f nilpotent; no hypothesis on f beyond R's carrier.",
	Deps: []registry.EntryLike{
		ring_localization.IsLocalizationOnDef,
		ring_localization.PowersMultiplicative,
		comm_monoid.MapPow,
		ring_ideal.RingUnitDef,
		HypersurfaceConstantHomomorphism,
		FxMinusOneRegular,
		FxMinusOneInverts,
		FxMinusOneFractions,
		FxMinusOneKernel,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
		},
		Conclusion: "is_localization_on(R, " +
			"    monoid_powers(R.mul, R.one, f), " +
			"    hypersurface_ring(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))), " +
			"    hypersurface_constant(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))))",
	},
		"unfold is_localization_on: the powers of f form a multiplicative set "+
			"(ring_localization.PowersMultiplicative); the constants are a ring homomorphism "+
			"(HypersurfaceConstantHomomorphism, f • x - 1 over R by FxMinusOneRegular); the class of f ^ n "+
			"is the n-th power of the class of f (MapPow), a unit inverted by the n-th power of the class "+
			"of x (FxMinusOneInverts); the last two conjuncts are FxMinusOneFractions and FxMinusOneKernel"),
})}

// LocalizationIsomorphicQuotient — the ring of fractions with the powers
// of f as denominators is R[x]/(f·x − 1), as R-algebras: a / 1 goes to
// the constant a and 1 / f to the class of x.
var LocalizationIsomorphicQuotient = localizationIsomorphicQuotientThm{family.Add(registry.ProofEntry{
	Name: "LocalizationIsomorphicQuotient",
	Key:  "prop_49b800871efd79c6",
	Reading: "R a commutative ring and f in its carrier are the hypotheses: f nilpotent or zero " +
		"makes both rings the zero ring, and f a unit makes both a copy of R. The second conjunct is " +
		"the R-algebra condition and alone pins h down on the fractions, the map out of a localization " +
		"being unique; the third, h(1 / f) the class of x, follows from it and is stated for use.",
	Deps: []registry.EntryLike{
		ring_localization.LocalizationIsomorphism,
		ring_localization.ToFractionIsLocalization,
		FxMinusOneIsLocalization,
		FxMinusOneInverts,
		ring_localization.DenominatorUnit,
		ring_localization.FractionClassDef,
		ring_localization.ToFractionDef,
		comm_monoid.MonoidPowersDef,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
		},
		Conclusion: "∃h:(set(prod(A, A)) → set(num → A)). " +
			"    ring_isomorphism(mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            ring_localization(R.carrier, monoid_powers(R.mul, R.one, f))), " +
			"        hypersurface_ring(R, vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0))), " +
			"        h) ∧ " +
			"    (∀a:A. " +
			"        a ∈ R.carrier ⇒ " +
			"        h(to_fraction(R.carrier, monoid_powers(R.mul, R.one, f), a)) = " +
			"        hypersurface_constant(R, " +
			"            vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), " +
			"            a)) ∧ " +
			"    h(fraction_class(R.carrier, monoid_powers(R.mul, R.one, f), R.one, f)) = " +
			"    hypersurface_projection(R, " +
			"        vec_sub(vec_scalar_mul(f, basis_vector(1)), basis_vector(0)), " +
			"        basis_vector(1))",
	},
		"ring_localization.LocalizationIsomorphism at ToFractionIsLocalization (the powers of "+
			"f a multiplicative set) and FxMinusOneIsLocalization gives h with h(a / 1) the class "+
			"of the constant a; 1 / f inverts f / 1 among the fractions (DenominatorUnit, f = f ^ "+
			"1 a power), so h(1 / f) inverts the class of f (MapMul, MapOne), and that inverse is "+
			"the class of x (FxMinusOneInverts, an inverse in a commutative ring being unique)"),
})}
