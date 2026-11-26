// etale.go — the cotangent side of the étale hypersurfaces. The tower
// R → R[x] → R[x]/(g) has the long exact sequence of transitivity. R[x]
// over R has its André–Quillen homology in degree 0 alone, N on the
// differential dx; R[x]/(g) over R[x] has it in degree 1 alone when g is
// no zero divisor, N on the conormal class of g. So the sequence has
// five terms, and its connecting map sends the conormal class of g with
// coefficient m to dx with coefficient g′·m — the differential of g, as
// the connecting map of every tower sends a conormal class to a
// differential. When the class of g′ is a unit, as it is for g
// separable, the connecting map is an isomorphism and every D_n of
// R[x]/(g) over R vanishes. The simple separable extension K(a) over K
// and the localization of R at the powers of f are such quotients, so
// theirs vanishes too.

package cotangent_examples

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// R[x] over R
// ---------------------------------------------------------------------------

// HypersurfaceKoszulQuotient — R[x]/(g) is the quotient of the ring R[x]
// by its element g, as the Koszul algebra's chapter spells it, with the
// same projection.
var HypersurfaceKoszulQuotient = hypersurfaceKoszulQuotientThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceKoszulQuotient",
	Key:  "prop_478130ef84d8baa3",
	Reading: "No hypothesis: once P's projections are read the two records are spelled alike, " +
		"ideal_span at P's fields being hypersurface_ideal(R, g); where R is no ring or g no polynomial " +
		"over R both sides unfold to the same degenerate record. It lets RegularQuotientCotangent and " +
		"RegularQuotientFirstHomology, stated for koszul_quotient, speak of R[x]/(g) over R[x].",
	Deps: []registry.EntryLike{
		HypersurfaceRingDef,
		hypersurfaceIdealDef,
		hypersurfaceProjectionDef,
		KoszulQuotientDef,
		KoszulProjectionDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀P:ring_ops(num → A). ∀g:(num → A).",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
		},
		Conclusion: "hypersurface_ring(R, g) = koszul_quotient(P, g) ∧ " +
			"hypersurface_projection(R, g) = koszul_projection(P, g)",
	},
		"unfold both sides (HypersurfaceRingDef, hypersurfaceIdealDef, KoszulQuotientDef; "+
			"hypersurfaceProjectionDef, KoszulProjectionDef, by extensionality): P's projections are "+
			"the operations and the carrier of the polynomials over R, so the ideal ideal_span spans "+
			"at them is hypersurface_ideal(R, g), and the records and the class maps are spelled alike"),
})}

// CorpusPolynomialCotangent — the polynomials over R in one variable x
// have their André–Quillen homology over R in degree 0 alone: with
// coefficients in N over any ring T that R[x] maps to, D_0(R[x]/R, N) is
// N, m going to the class of dx with coefficient m, and D_n(R[x]/R, N)
// vanishes for n ≥ 1.
var CorpusPolynomialCotangent = corpusPolynomialCotangentThm{family.Add(registry.ProofEntry{
	Name: "CorpusPolynomialCotangent",
	Key:  "prop_727ee3e9c755c199",
	Reading: "The coefficients are any module over any ring T that R[x] maps to, as the tower R → " +
		"R[x] → T reads them; with T = R[x] and h the identity, D_0(R[x]/R, N) is Ω_{R[x]/R} ⊗ N, free " +
		"on dx. The variable x is basis_vector(1), and its name in the standard resolution is " +
		"carrier_tag(P.carrier, x). R[x] lives on num → A, and U needs room for its carrier, the " +
		"polynomials over R, as well as for R's: that is P's universe hypothesis, kept beside R's " +
		"though over a ring R it follows from it (at a powerset host, PolynomialRingCotangentUniverse); " +
		"under it the naming of P's carrier is injective there and the name of x is a name of degree 0. " +
		"h a ring map makes the one of R[x] act on N as the identity. T need not be a quotient of R[x]. " +
		"Over the zero ring R[x], T and N are zero and both sides are one point.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentResolutionIndependence,
		cotangent_complex.CotangentHomologyDef,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialBoundaryDef,
		simplicial_ring.ConstantPolynomialAlgebra,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_module.AcyclicAugmentation,
		simplicial_module.MooreTermsDef,
		simplicial_module.ConstantFaceComplexHomology,
		free_algebra.PolynomialOneVariableHomomorphism,
		free_algebra.PolynomialOneVariableInjective,
		free_algebra.PolynomialOneVariableOnto,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		partial_derivative.JacobianIdentity,
		partial_derivative.JacobianDelta,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyTrivialIffExact,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.HomCompose,
		EmptyNamesResolution,
		ConstantDifferentialComplex,
		StandardDifferentialBoundaryOne,
		cotangent_complex.CotangentCoefficientRestriction,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:ring_ops(num → A). " +
			"∀T:ring_ops(C). " +
			"∀h:((num → A) → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"ring_homomorphism(P, T, h)",
			"module_on(T, N)",
		},
		Conclusion: "module_isomorphism(T, " +
			"    N, " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        T, " +
			"        h, " +
			"        N, " +
			"        0), " +
			"    λm:D. " +
			"        left_coset(fun_add(N.add), " +
			"            delta_at(N.zero, m, carrier_tag(P.carrier, basis_vector(R.zero, R.one, 1))), " +
			"            boundaries(cotangent_complex(R, " +
			"                    P, " +
			"                    λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"                    T, " +
			"                    h, " +
			"                    N), " +
			"                0))) ∧ " +
			"(∀n:num. " +
			"    1 ≤ n ⇒ " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        T, " +
			"        h, " +
			"        N, " +
			"        n).carrier = " +
			"    {cotangent_homology(R, " +
			"            P, " +
			"            λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"            T, " +
			"            h, " +
			"            N, " +
			"            n).zero})",
	},
		"take a name u in U. The constant algebra on {u}, every face and degeneracy the identity, is a "+
			"polynomial simplicial algebra (ConstantPolynomialAlgebra), and evaluation at x, "+
			"universe_algebra_eval(R, P, constants, λv. x), augments it over R[x]: a ring map carrying the "+
			"constant a to the constant polynomial a (FreeAlgebraEvalHom, FreeAlgebraEvalConst), inverse to "+
			"the one-variable map at the name u along the universe's embedding "+
			"(PolynomialOneVariableHomomorphism, PolynomialOneVariableInjective, PolynomialOneVariableOnto, "+
			"FreeAlgebraEvalVar, FreeAlgebraEvalUnique), so onto P's carrier and injective on the algebra "+
			"on {u}. Its Moore terms vanish above degree 0, so it is a polynomial resolution of R[x] "+
			"(PolynomialResolution, AcyclicAugmentation, MooreTermsDef, as in EmptyNamesResolution). "+
			"CotangentResolutionIndependence, the coefficients through h, gives a comparison F into the "+
			"standard resolution and a chain homotopy equivalence from its differential complex, the face "+
			"complex of the constant simplicial module of functions on {u} into N — every face's Jacobian "+
			"is the identity (JacobianIdentity, as in ConstantDifferentialComplex) — onto the cotangent "+
			"complex. That homology is N in degree 0, on the basis differential at u, and zero above "+
			"(ConstantFaceComplexHomology, ChainHomotopyEquivalenceQuasiIsomorphism, "+
			"HomologyTrivialIffExact). The image of the basis differential at u with coefficient m is the "+
			"differential of F(0, var(u)) with coefficient m (JacobianDelta), a member of the degree-0 "+
			"algebra whose augmentation is x; StandardDifferentialBoundaryOne, at N restricted to R[x] "+
			"along h and carried to these coefficients by CotangentCoefficientRestriction, makes its class "+
			"that of the basis differential at carrier_tag(P.carrier, x) with coefficient m"),
})}

// CorpusPolynomialDifferential — in D_0(R[x]/R, N) the basis
// differential at a polynomial p has the class of dx with coefficient
// p′·m: d(p) = p′(x) dx.
var CorpusPolynomialDifferential = corpusPolynomialDifferentialThm{family.Add(registry.ProofEntry{
	Name: "CorpusPolynomialDifferential",
	Key:  "prop_d1fb0cfbdf13d59b",
	Reading: "It is d(p) = p′(x) dx in Ω_{R[x]/R} ⊗ N, read in D_0. p over R is " +
		"load-bearing: off the polynomials carrier_tag(P.carrier, p) is unspecified, possibly " +
		"the name of another polynomial. A constant has derivative zero, and its basis " +
		"differential is a boundary, that of the negated basis differential at the constant; at " +
		"p = x the derivative is basis_vector(0), R[x]'s one, and the two sides are one class.",
	Deps: []registry.EntryLike{
		StandardDifferentialBoundaryOne,
		partial_derivative.PartialDerivativeTransport,
		partial_derivative.PartialSupportFinite,
		free_algebra.PolynomialOneVariableHomomorphism,
		free_algebra.FreeAlgebraSubset,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		standard_resolution.StandardNamesDef,
		standard_resolution.StandardTermsDef,
		standard_resolution.StandardEpsDef,
		standard_resolution.StandardEpsHom,
		polynomial.PolynomialExpansion,
		polynomial.DerivativeOver,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.CotangentCoefficientRestriction,
		chain_complex.BoundariesDef,
		module.ModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:ring_ops(num → A). " +
			"∀T:ring_ops(C). " +
			"∀h:((num → A) → C). " +
			"∀N:module_ops(C, D). " +
			"∀p:(num → A). " +
			"∀m:D.",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"ring_homomorphism(P, T, h)",
			"module_on(T, N)",
			"polynomial_over(R.carrier, p)",
			"m ∈ N.carrier",
		},
		Conclusion: "left_coset(fun_add(N.add), " +
			"    delta_at(N.zero, m, carrier_tag(P.carrier, p)), " +
			"    boundaries(cotangent_complex⟨U:U⟩(R, " +
			"            P, " +
			"            λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"            T, " +
			"            h, " +
			"            N), " +
			"        0)) = " +
			"left_coset(fun_add(N.add), " +
			"    delta_at(N.zero, " +
			"        N.smul(h(polynomial_derivative(p)), m), " +
			"        carrier_tag(P.carrier, basis_vector(R.zero, R.one, 1))), " +
			"    boundaries(cotangent_complex(R, " +
			"            P, " +
			"            λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"            T, " +
			"            h, " +
			"            N), " +
			"        0))",
	},
		"the one-variable map at the name carrier_tag(P.carrier, x), along the universe's embedding, "+
			"sends p to a member w of the algebra on {carrier_tag(P.carrier, x)}, which lies in the "+
			"degree-0 algebra of the standard resolution (PolynomialOneVariableHomomorphism, "+
			"FreeAlgebraSubset, StandardNamesDef, StandardTermsDef); its augmentation is p, evaluation "+
			"reading x at that name (StandardEpsDef, FreeAlgebraEvalVar, FreeAlgebraEvalUnique, "+
			"PolynomialExpansion). By StandardDifferentialBoundaryOne, at N restricted to R[x] along h "+
			"and carried to these coefficients by CotangentCoefficientRestriction, the differential of w "+
			"with coefficient m differs by a boundary from the basis differential at "+
			"carrier_tag(P.carrier, p) with coefficient m. That differential has one term, at "+
			"carrier_tag(P.carrier, x) (PartialSupportFinite): the partial derivative there is the "+
			"one-variable image of polynomial_derivative(p) (PartialDerivativeTransport), whose "+
			"augmentation is polynomial_derivative(p) (DerivativeOver), so the term is h of it acting on m"),
})}

// ---------------------------------------------------------------------------
// The connecting map on conormal classes
// ---------------------------------------------------------------------------

// TransitivityConnectingConormal — for a tower R → S → T and x in S
// killed by g, the connecting map D_1(T/S, N) → D_0(S/R, N) sends the
// class of the conormal cycle of x with coefficient m to the class of dx
// with coefficient m.
var TransitivityConnectingConormal = transitivityConnectingConormalThm{family.Add(registry.ProofEntry{
	Name: "TransitivityConnectingConormal",
	Key:  "prop_cdb952fcab2b6ae3",
	Reading: "No sign: the vertical boundary out of (0, 1) enters the total boundary with " +
		"alternating_sign(0) = T.one, connecting_hom takes the preimage of the boundary of a lift as it " +
		"is, and the conormal cycle is d(var(x) − var(0)) with no sign, as conormal_map has it. With N " +
		"= T and m = T.one it says the connecting map sends conormal_map(S, T, g, x) to the class of dx " +
		"⊗ 1: the map I/I² → Ω_{S/R} ⊗_S T of the conormal sequence, x ↦ dx. Of x only g(x) = T.zero is " +
		"read; g need not be onto. g(x) = T.zero = g(S.zero) is what sends both second-tag variables to " +
		"one name, so that the lift is a cycle of the right total; S's universe makes standard_eps read " +
		"carrier_tag(S.carrier, x) back as x. At x = S.zero both sides are the zero class.",
	Deps: []registry.EntryLike{
		transitivity.TransitivityConnectingDef,
		transitivity.RightTotalQuasiIsomorphism,
		transitivity.LeftTotalQuasiIsomorphism,
		transitivity.TriangleTotalShortExact,
		transitivity.TriangleRightTotalDef,
		cotangent_complex.CotangentCoefficientRestriction,
		transitivity.TriangleMiddleTotalDef,
		transitivity.TriangleLeftTotalDef,
		transitivity.TriangleRightEpsDef,
		transitivity.TriangleRowAugmentationDef,
		transitivity.TriangleRightVerticalDef,
		transitivity.TriangleVerticalDef,
		transitivity.TriangleSectionDef,
		transitivity.TriangleProjectionDef,
		transitivity.TriangleInclusionDef,
		transitivity.TriangleLeftEpsDef,
		standard_resolution.RelativeNamesDef,
		standard_resolution.RelativeVerticalFaceDef,
		standard_resolution.RelativeVerticalEpsDef,
		standard_resolution.StandardToBaseDef,
		chain_complex.DoubleBoundaryDef,
		chain_complex.DoubleEdgeDef,
		chain_complex.ConnectingHomDef,
		chain_complex.ConnectingHomCoset,
		chain_complex.HomologyMapCoset,
		cotangent_complex.DifferentialBoundaryDef,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		partial_derivative.PartialConst,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		functions.InverseOnLeft,
		conormalCycleDef,
		ConormalCycleIsCycle,
		StandardDifferentialBoundaryOne,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀x:B. " +
			"∀m:D.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"x ∈ S.carrier",
			"g(x) = T.zero",
			"m ∈ N.carrier",
		},
		Conclusion: "transitivity_connecting(R, " +
			"    S, " +
			"    f, " +
			"    T, " +
			"    g, " +
			"    N, " +
			"    0, " +
			"    left_coset(fun_add(N.add), " +
			"        λy:U. N.smul(conormal_cycle(S, T, x, y), m), " +
			"        boundaries(cotangent_complex(S, T, g, T, λc:C. c, N), 1))) = " +
			"left_coset(fun_add(N.add), " +
			"    delta_at(N.zero, m, carrier_tag(S.carrier, x)), " +
			"    boundaries(cotangent_complex(R, S, f, T, g, N), 0))",
	},
		"the class on the left is that of the differential of the 1-simplex var(c(x)) − var(c(0)) of "+
			"the standard resolution of T over S with coefficient m, a cycle because d_1 sends both "+
			"variables to var(tag(T.zero)) (conormalCycleDef, as in ConormalCycleIsCycle). In the right "+
			"total, the diagonal u with u(1) zero and u(0) the function on the relative names of (0, 1) "+
			"taking m at var(tag₀ c(x)) and its negation at var(tag₀ c(S.zero)) is a cycle with that right "+
			"edge: the row augmentation sends the variable of tag₀ c(s) to the constant s "+
			"(TriangleRightEpsDef, TriangleRowAugmentationDef, StandardToBaseDef), and the vertical "+
			"boundary of the section of u(0) has no second-tag part, since d_0 sends the variable of the "+
			"second tag of var(tag₀ c(s)) to that first-tag variable and d_1 to var(tag₁ c(g(s))), which is "+
			"var(tag₁ c(T.zero)) for s = x and for s = S.zero alike (TriangleRightVerticalDef, "+
			"TriangleVerticalDef, RelativeVerticalFaceDef, RelativeVerticalEpsDef, DifferentialBoundaryDef, "+
			"JacobianDelta, PartialVar, TagsDisjoint). So the inverse of the right edge's homology map "+
			"gives the class of u (RightTotalQuasiIsomorphism, InverseOnLeft). Lift u to the middle total "+
			"by the section (TriangleSectionDef, TriangleProjectionDef): its total boundary at coordinate 0 "+
			"is that vertical boundary with the sign T.one (DoubleBoundaryDef), the basis differential at "+
			"tag₀ c(x) less the one at tag₀ c(S.zero), both with coefficient m — a member of the left "+
			"total, its own image under the inclusion (TriangleInclusionDef, ConnectingHomDef, "+
			"ConnectingHomCoset). The left edge untags it (DoubleEdgeDef, TriangleLeftEpsDef, "+
			"TagInjective), and the basis differential at carrier_tag(S.carrier, S.zero) is a boundary of "+
			"the cotangent complex of S over R, that of the negated basis differential at the constant zero "+
			"(StandardDifferentialBoundaryOne at N restricted to S along g, "+
			"CotangentCoefficientRestriction, PartialConst); the classes agree, the left edge being a chain "+
			"map (TransitivityConnectingDef, LeftTotalQuasiIsomorphism, HomologyMapCoset)"),
})}

// ---------------------------------------------------------------------------
// The tower R → R[x] → R[x]/(g)
// ---------------------------------------------------------------------------

// HypersurfaceTriangle — for g no zero divisor, the long exact sequence
// of the tower R → R[x] → R[x]/(g) has five terms, 0 → D_1(T/R, N) →
// D_1(T/R[x], N) → D_0(R[x]/R, N) → D_0(T/R, N) → 0 with T = R[x]/(g),
// and D_n(T/R, N) vanishes for n ≥ 2.
var HypersurfaceTriangle = hypersurfaceTriangleThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceTriangle",
	Key:  "prop_21f96343dd2f3a69",
	Reading: "The left terms D_n(R[x]/R, N) live in degree 0 and the right terms D_n(T/R[x], N) in " +
		"degree 1, so the long exact sequence of the tower keeps five terms. T's structure map over R " +
		"is hypersurface_constant(R, g), the projection after the constants (hypersurfaceConstantDef), " +
		"which is the composite the transitivity maps read. Only the first conjunct reads regularity, " +
		"through the vanishing of D_n(T/R[x], N) above degree 1 (RegularQuotientCotangent); the other " +
		"four hold for every polynomial g over R, D_0(T/R[x], N) vanishing because the projection is " +
		"onto. At a powerset host the universes for R[x] and for T follow from R's " +
		"(PolynomialRingCotangentUniverse; QuotientCotangentUniverse through HypersurfaceKoszulQuotient " +
		"and KoszulQuotientIdealQuotient), so a host chosen for R alone serves the tower.",
	Deps: []registry.EntryLike{
		transitivity.TransitivityExactAtMiddle,
		transitivity.TransitivityExactAtRight,
		transitivity.TransitivityExactAtLeft,
		transitivity.TransitivityEnd,
		CorpusPolynomialCotangent,
		RegularQuotientCotangent,
		ConormalDegreeZero,
		HypersurfaceKoszulQuotient,
		HypersurfaceRingOn,
		HypersurfaceProjectionHomomorphism,
		hypersurfaceConstantDef,
		polynomial.PolynomialRingOn,
		polynomial.BasisVectorMul,
		polynomial.BasisVectorOver,
		module_homomorphism.ExactAtDef,
		cotangent_complex.CotangentHomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀P:ring_ops(num → A). ∀g:(num → A). ∀N:module_ops(set(num → A), D).",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(hypersurface_ring(R, g), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"module_on(hypersurface_ring(R, g), N)",
			"∀q:(num → A). " +
				"    polynomial_over(R.carrier, q) ∧ polynomial_mul(g, q) = vec_zero(R.zero) ⇒ " +
				"    q = vec_zero(R.zero)",
		},
		Conclusion: "(∀n:num. " +
			"    2 ≤ n ⇒ " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_constant(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        n).carrier = " +
			"    {cotangent_homology(R, " +
			"            hypersurface_ring(R, g), " +
			"            hypersurface_constant(R, g), " +
			"            hypersurface_ring(R, g), " +
			"            λy:set(num → A). y, " +
			"            N, " +
			"            n).zero}) ∧ " +
			"(∀c:set(U → D). " +
			"    c ∈ " +
			"    cotangent_homology(R, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_constant(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1).carrier ∧ " +
			"    transitivity_right_map(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        1)(c) = " +
			"    cotangent_homology(P, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1).zero ⇒ " +
			"    c = " +
			"    cotangent_homology(R, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_constant(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1).zero) ∧ " +
			"exact_at(cotangent_homology⟨U:U⟩(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0).zero, " +
			"    cotangent_homology(R, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_constant(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1).carrier, " +
			"    cotangent_homology(P, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1).carrier, " +
			"    transitivity_right_map(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        1), " +
			"    transitivity_connecting(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0)) ∧ " +
			"exact_at(cotangent_homology⟨U:U⟩(R, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_constant(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        0).zero, " +
			"    cotangent_homology(P, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1).carrier, " +
			"    cotangent_homology(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0).carrier, " +
			"    transitivity_connecting(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0), " +
			"    transitivity_left_map(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0)) ∧ " +
			"image(transitivity_left_map(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0), " +
			"    cotangent_homology⟨U:U⟩(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0).carrier) = " +
			"cotangent_homology(R, " +
			"    hypersurface_ring(R, g), " +
			"    hypersurface_constant(R, g), " +
			"    hypersurface_ring(R, g), " +
			"    λy:set(num → A). y, " +
			"    N, " +
			"    0).carrier",
	},
		"the constants are a ring map from R to R[x] (BasisVectorMul, BasisVectorOver and the laws of "+
			"PolynomialRingOn) and the projection one onto T (HypersurfaceProjectionHomomorphism, "+
			"HypersurfaceRingOn), and T's structure map is their composite (hypersurfaceConstantDef), so the "+
			"transitivity sequence of the tower applies. Its outer terms: D_n(R[x]/R, N) vanishes for n ≥ 1 "+
			"(CorpusPolynomialCotangent, the coefficients through the projection); T is koszul_quotient(P, "+
			"g) with the projection koszul_projection(P, g) (HypersurfaceKoszulQuotient), P a commutative "+
			"ring in which g is no zero divisor, so D_n(T/R[x], N) vanishes for n ≥ 2 "+
			"(RegularQuotientCotangent at P), and D_0(T/R[x], N) vanishes, the projection being onto "+
			"(ConormalDegreeZero). For n ≥ 2 the right map lands in the kernel of the connecting map out of "+
			"D_n(T/R[x], N) (TransitivityExactAtRight at n − 1, ExactAtDef), a part of that zero module, so "+
			"its kernel is all of D_n(T/R, N); that kernel is the image of the zero module D_n(R[x]/R, N) "+
			"(TransitivityExactAtMiddle), one point, so D_n(T/R, N) is its zero. In degree 1 the kernel of "+
			"the left map out of D_1(R[x]/R, N) = {zero} is the image of D_2(T/R[x], N), not empty "+
			"(TransitivityExactAtLeft at n = 1), so the left map keeps the zero, and the kernel of the right "+
			"map is the image of {zero}, the zero alone (TransitivityExactAtMiddle). The two exact_at are "+
			"TransitivityExactAtRight and TransitivityExactAtLeft at n = 0. In degree 0 the right map lands "+
			"in D_0(T/R[x], N) = {zero} (TransitivityEnd), so its kernel is all of D_0(T/R, N), the image of "+
			"the left map (TransitivityExactAtMiddle)"),
})}

// HypersurfaceConnectingMap — the connecting map of the tower sends the
// conormal class of g with coefficient m to the class of dx with
// coefficient g′·m: the differential of g.
var HypersurfaceConnectingMap = hypersurfaceConnectingMapThm{family.Add(registry.ProofEntry{
	Name: "HypersurfaceConnectingMap",
	Key:  "prop_820710b24ddd7780",
	Reading: "Of g only that it is a polynomial over R is read: the connecting map " +
		"is d(g) = g′(x) dx whatever g is. With N = T and m = T.one it sends " +
		"conormal_map(P, T, projection, g), the class of g in (g)/(g²), to dx with " +
		"coefficient the class of g′. At g = vec_zero both sides are the zero class: the " +
		"conormal cycle of R[x]'s zero is the zero function and the derivative is zero.",
	Deps: []registry.EntryLike{
		TransitivityConnectingConormal,
		CorpusPolynomialDifferential,
		HypersurfaceIdealDivides,
		HypersurfaceRingDef,
		hypersurfaceProjectionDef,
		HypersurfaceProjectionHomomorphism,
		HypersurfaceRingOn,
		quotient_ring.CosetEqIdealIff,
		polynomial.PolynomialRingOn,
		polynomial.BasisVectorMul,
		polynomial.BasisVectorOver,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:ring_ops(num → A). " +
			"∀g:(num → A). " +
			"∀N:module_ops(set(num → A), D). " +
			"∀m:D.",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(hypersurface_ring(R, g), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"module_on(hypersurface_ring(R, g), N)",
			"m ∈ N.carrier",
		},
		Conclusion: "transitivity_connecting(R, " +
			"    P, " +
			"    λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"    hypersurface_ring(R, g), " +
			"    hypersurface_projection(R, g), " +
			"    N, " +
			"    0)(left_coset(fun_add(N.add), " +
			"        λy:U. N.smul(conormal_cycle(P, hypersurface_ring(R, g), g, y), m), " +
			"        boundaries(cotangent_complex(P, " +
			"                hypersurface_ring(R, g), " +
			"                hypersurface_projection(R, g), " +
			"                hypersurface_ring(R, g), " +
			"                λy:set(num → A). y, " +
			"                N), " +
			"            1))) = " +
			"left_coset(fun_add(N.add), " +
			"    delta_at(N.zero, " +
			"        N.smul(hypersurface_projection(R, g, polynomial_derivative(g)), m), " +
			"        carrier_tag(P.carrier, basis_vector(R.zero, R.one, 1))), " +
			"    boundaries(cotangent_complex(R, " +
			"            P, " +
			"            λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"            hypersurface_ring(R, g), " +
			"            hypersurface_projection(R, g), " +
			"            N), " +
			"        0))",
	},
		"TransitivityConnectingConormal at the tower, its maps ring maps as in HypersurfaceTriangle, "+
			"and at x = g: g is a polynomial over R lying in its own ideal, so its class is the ideal, "+
			"the quotient's zero (HypersurfaceIdealDivides, hypersurfaceProjectionDef, CosetEqIdealIff, "+
			"HypersurfaceRingDef); it gives the class of the basis differential at carrier_tag(P.carrier, "+
			"g) with coefficient m, which CorpusPolynomialDifferential at p = g, the coefficients through "+
			"the projection, turns into the class of dx with coefficient the class of g′ acting on m"),
})}

// UnitMultipleIsomorphism — when g is no zero divisor and its derivative
// is a unit modulo g, the connecting map D_1(T/R[x], N) → D_0(R[x]/R, N)
// is an isomorphism: both sides are N and the map is multiplication by
// the unit g′.
var UnitMultipleIsomorphism = unitMultipleIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "UnitMultipleIsomorphism",
	Key:  "prop_a48c241ca31ba77b",
	Reading: "The unit is load-bearing: it makes multiplication by the class of g′ a " +
		"bijection of N. Regularity, which makes D_1(T/R[x], N) one copy of N on the conormal " +
		"class of g, follows from it: if g·q = 0 with q ≠ 0, McCoy's theorem gives r ≠ 0 in R " +
		"with r·g = 0, then r·g′ = 0, and r = r·(v·g′ − w·g) = 0 for the v, w over R the unit " +
		"provides. It is kept as a hypothesis because RegularQuotientFirstHomology reads it. " +
		"At g a unit of R[x], T is the zero ring and both modules are one point.",
	Deps: []registry.EntryLike{
		HypersurfaceConnectingMap,
		RegularQuotientFirstHomology,
		CorpusPolynomialCotangent,
		HypersurfaceKoszulQuotient,
		HypersurfaceRingOn,
		polynomial.PolynomialRingOn,
		ring_ideal.RingUnitDef,
		module.ModuleOn,
		module.SmulMul,
		module.SmulOne,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.HomCompose,
		cotangent_complex.CotangentHomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀P:ring_ops(num → A). ∀g:(num → A). ∀N:module_ops(set(num → A), D).",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(hypersurface_ring(R, g), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"module_on(hypersurface_ring(R, g), N)",
			"∀q:(num → A). " +
				"    polynomial_over(R.carrier, q) ∧ polynomial_mul(g, q) = vec_zero(R.zero) ⇒ " +
				"    q = vec_zero(R.zero)",
			"ring_unit(hypersurface_ring(R, g), hypersurface_projection(R, g, polynomial_derivative(g)))",
		},
		Conclusion: "module_isomorphism(hypersurface_ring(R, g), " +
			"    cotangent_homology⟨U:U⟩(P, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        1), " +
			"    cotangent_homology(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0), " +
			"    transitivity_connecting(R, " +
			"        P, " +
			"        λa:A. vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_projection(R, g), " +
			"        N, " +
			"        0))",
	},
		"RegularQuotientFirstHomology at P (HypersurfaceKoszulQuotient, PolynomialRingOn) makes m ↦ "+
			"the conormal class of g with coefficient m an isomorphism γ₁ of N onto D_1(T/R[x], N); "+
			"CorpusPolynomialCotangent, the coefficients through the projection, makes m ↦ the class of dx "+
			"with coefficient m an isomorphism γ₀ of N onto D_0(R[x]/R, N); HypersurfaceConnectingMap says "+
			"the connecting map sends γ₁(m) to γ₀(u • m), u the class of g′. Multiplication by the unit u "+
			"is an isomorphism of N over the commutative ring T, inverted by multiplication by u's inverse "+
			"(RingUnitDef, SmulMul, SmulOne, HypersurfaceRingOn). Every member of D_1(T/R[x], N) is γ₁(m) "+
			"for one m, so there the connecting map is γ₀ after multiplication by u after the inverse of "+
			"γ₁, a composite of isomorphisms (IsomorphismInverse, HomCompose, ModuleIsomorphismDef)"),
})}

// EtaleHypersurfaceVanishes — when g is no zero divisor and separable,
// R[x]/(g) has no André–Quillen homology over R: D_n(R[x]/(g) / R, N) = 0
// for every n and every module N over R[x]/(g).
var EtaleHypersurfaceVanishes = etaleHypersurfaceVanishesThm{family.Add(registry.ProofEntry{
	Name: "EtaleHypersurfaceVanishes",
	Key:  "prop_3f53dbd4a3b9dc90",
	Reading: "In degree 0 it says Ω_{T/R} = 0, T unramified over R; with the higher vanishing, T is " +
		"étale over R. Separability is load-bearing: at g = x² over a field of characteristic other than " +
		"2 the derivative 2x is no unit modulo x², and D_0 is Ω_{T/R} ⊗ N = N/2xN, not zero for N = T. " +
		"Regularity follows from separability by McCoy's theorem, as in UnitMultipleIsomorphism from u·g " +
		"+ v·g′ = 1, and is kept for the cards it is read through. P is bound only to name R[x] in the " +
		"hypotheses: the universe U must have room for it. Over the zero ring every module is one point.",
	Deps: []registry.EntryLike{
		HypersurfaceTriangle,
		UnitMultipleIsomorphism,
		SeparableIffDerivativeUnit,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleIsomorphismDef,
		cotangent_complex.CotangentHomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:ring_ops(num → A). " +
			"∀g:(num → A). " +
			"∀N:module_ops(set(num → A), D). " +
			"∀n:num.",
		Hypotheses: []string{
			"P = polynomial_ring(R)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(hypersurface_ring(R, g), 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"module_on(hypersurface_ring(R, g), N)",
			"∀q:(num → A). " +
				"    polynomial_over(R.carrier, q) ∧ polynomial_mul(g, q) = vec_zero(R.zero) ⇒ " +
				"    q = vec_zero(R.zero)",
			"polynomial_separable(R, g)",
		},
		Conclusion: "cotangent_homology⟨U:U⟩(R, " +
			"    hypersurface_ring(R, g), " +
			"    hypersurface_constant(R, g), " +
			"    hypersurface_ring(R, g), " +
			"    λy:set(num → A). y, " +
			"    N, " +
			"    n).carrier = " +
			"{cotangent_homology(R, " +
			"        hypersurface_ring(R, g), " +
			"        hypersurface_constant(R, g), " +
			"        hypersurface_ring(R, g), " +
			"        λy:set(num → A). y, " +
			"        N, " +
			"        n).zero}",
	},
		"g separable makes the class of g′ a unit of T (SeparableIffDerivativeUnit), so the "+
			"connecting map D_1(T/R[x], N) → D_0(R[x]/R, N) is a bijection "+
			"(UnitMultipleIsomorphism). With HypersurfaceTriangle: above degree 1 D_n(T/R, N) "+
			"is zero. In degree 1 the right map is injective and its image is the kernel of the "+
			"connecting map, which is zero, so D_1(T/R, N) is zero. In degree 0 every member of "+
			"D_0(R[x]/R, N) is in the image of the connecting map, the kernel of the left map, "+
			"so the left map is constant at the zero, and it is onto D_0(T/R, N) (ExactAtDef)"),
})}

// ---------------------------------------------------------------------------
// The two instances
// ---------------------------------------------------------------------------

// SimpleSeparableExtensionCotangentVanishes — a simple separable
// algebraic extension K(a) of K has no André–Quillen homology over K:
// D_n(K(a)/K, N) = 0 for every n and every module N over K(a).
var SimpleSeparableExtensionCotangentVanishes = simpleSeparableExtensionCotangentVanishesThm{family.Add(registry.ProofEntry{
	Name: "SimpleSeparableExtensionCotangentVanishes",
	Key:  "prop_d75ef840d24f3adb",
	Reading: "The universe is fixed rather than assumed, and chosen from A alone: the proof reads " +
		"K[x] on num → A and K[x]/(μ) on set(num → A) beside K and K(a), the second on a type the host " +
		"need not fit; their carriers have room wherever K's does (PolynomialRingCotangentUniverse, " +
		"QuotientCotangentUniverse). Separability is load-bearing: for a = t^{1/p} over 𝔽_p(t) the " +
		"minimal polynomial x^p − t has derivative zero and D_0 = Ω_{K(a)/K} is K(a) da, not zero. So " +
		"is algebraicity: for a transcendental a the minimal polynomial is a sequence nothing is said " +
		"of. At a in K the minimal polynomial is x − a and the statement is D_n(K/K, N) = 0.",
	Deps: []registry.EntryLike{
		EtaleHypersurfaceVanishes,
		AdjoinIsomorphicQuotient,
		MinimalPolynomialRegular,
		HypersurfaceConstantHomomorphism,
		cotangent_complex.CotangentIsomorphismInvariance,
		cotangent_complex.CotangentCoefficientRestriction,
		simplicial_ring.PowerSetUniverse,
		simplicial_ring.PolynomialRingCotangentUniverse,
		simplicial_ring.QuotientCotangentUniverse,
		HypersurfaceKoszulQuotient,
		KoszulQuotientIdealQuotient,
		cardinal.LeftFactorIntoPowerSet,
		cardinal.CardLeSubset,
		cardinal.CardLeTrans,
		algebraic_element.MinimalPolynomialSpec,
		algebraic_element.AdjoinSubfield,
		field.SubfieldFieldOn,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.RingIsomorphismDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀N:module_ops(A, D). ∀n:num.",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"algebraic_over(L, K, a)",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
			"module_on(restrict_ring(field_ring(L), field_adjoin(L, K, {a})), N)",
		},
		Conclusion: "cotangent_homology⟨U:set(prod(num, prod(A, A)))⟩(restrict_ring(field_ring(L), K), " +
			"    restrict_ring(field_ring(L), field_adjoin(L, K, {a})), " +
			"    λk:A. k, " +
			"    restrict_ring(field_ring(L), field_adjoin(L, K, {a})), " +
			"    λy:A. y, " +
			"    N, " +
			"    n).carrier = " +
			"{cotangent_homology(restrict_ring(field_ring(L), K), " +
			"        restrict_ring(field_ring(L), field_adjoin(L, K, {a})), " +
			"        λk:A. k, " +
			"        restrict_ring(field_ring(L), field_adjoin(L, K, {a})), " +
			"        λy:A. y, " +
			"        N, " +
			"        n).zero}",
	},
		"U is a universe for K and K(a), their carriers sets of A's members, which inject into it "+
			"(LeftFactorIntoPowerSet, CardLeSubset, CardLeTrans, PowerSetUniverse); for K[x] it is one by "+
			"PolynomialRingCotangentUniverse, and for K[x]/(μ), μ the minimal polynomial, by "+
			"QuotientCotangentUniverse, the quotient being koszul_quotient(K[x], μ), an ideal quotient "+
			"(HypersurfaceKoszulQuotient, KoszulQuotientIdealQuotient). μ is over K "+
			"(MinimalPolynomialSpec), no zero divisor (MinimalPolynomialRegular) and separable, K a "+
			"commutative ring (SubfieldFieldOn), so EtaleHypersurfaceVanishes kills D_n(K[x]/(μ) / K, N') "+
			"for every module N' over the quotient. φ = induced_map(evaluation at a) is a ring isomorphism "+
			"from K[x]/(μ) onto K(a) carrying the class of the constant k to k (AdjoinIsomorphicQuotient); "+
			"the constants are a ring map into the quotient (HypersurfaceConstantHomomorphism) and K lies "+
			"in K(a) (AdjoinSubfield). CotangentIsomorphismInvariance, the coefficients K(a) through the "+
			"identity (RingHomIdentity), makes D_n(K(a)/K, N) isomorphic to D_n(K[x]/(μ) / K, N) with the "+
			"coefficients through φ, whose carrier and zero are those with N restricted to the quotient "+
			"along φ (CotangentCoefficientRestriction); that one is zero, and a bijection of carriers "+
			"keeps a carrier one point (ModuleIsomorphismDef)"),
})}

// LocalizationCotangentVanishes — the localization of R at the powers of
// f has no André–Quillen homology over R: D_n(R_f/R, N) = 0 for every n
// and every module N over R_f.
var LocalizationCotangentVanishes = localizationCotangentVanishesThm{family.Add(registry.ProofEntry{
	Name: "LocalizationCotangentVanishes",
	Key:  "prop_bc3cac540659ce9",
	Reading: "No hypothesis on f beyond R's carrier: f nilpotent or zero makes R_f the zero ring, f " +
		"a unit makes it a copy of R, and the vanishing holds in each. In degree 0 it says Ω_{R_f/R} = " +
		"0. The universe is fixed, and chosen from A alone, for the reason " +
		"SimpleSeparableExtensionCotangentVanishes gives; the fractions live on set(prod(A, A)), and as " +
		"a localization of R they have room wherever R's carrier does (LocalizationCotangentUniverse).",
	Deps: []registry.EntryLike{
		EtaleHypersurfaceVanishes,
		LocalizationIsomorphicQuotient,
		FxMinusOneRegular,
		FxMinusOneSeparable,
		HypersurfaceConstantHomomorphism,
		cotangent_complex.CotangentIsomorphismInvariance,
		cotangent_complex.CotangentCoefficientRestriction,
		simplicial_ring.PowerSetUniverse,
		simplicial_ring.PolynomialRingCotangentUniverse,
		simplicial_ring.QuotientCotangentUniverse,
		simplicial_ring.LocalizationCotangentUniverse,
		HypersurfaceKoszulQuotient,
		KoszulQuotientIdealQuotient,
		ring_localization.ToFractionIsLocalization,
		cardinal.LeftFactorIntoPowerSet,
		cardinal.CardLeSubset,
		cardinal.CardLeTrans,
		ring_homomorphism.IsomorphismInverse,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.RingIsomorphismDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A. ∀N:module_ops(set(prod(A, A)), D). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
			"module_on(mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
				"        fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
				"        fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
				"        fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
				"        fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
				"        fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
				"        ring_localization(R.carrier, monoid_powers(R.mul, R.one, f))), " +
				"    N)",
		},
		Conclusion: "cotangent_homology⟨U:set(prod(num, prod(A, A)))⟩(R, " +
			"    mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        ring_localization(R.carrier, monoid_powers(R.mul, R.one, f))), " +
			"    to_fraction(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"    mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        ring_localization(R.carrier, monoid_powers(R.mul, R.one, f))), " +
			"    λy:set(prod(A, A)). y, " +
			"    N, " +
			"    n).carrier = " +
			"{cotangent_homology(R, " +
			"        mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            ring_localization(R.carrier, monoid_powers(R.mul, R.one, f))), " +
			"        to_fraction(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"        mk_ring(fraction_add(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_zero(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_neg(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_mul(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_one(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            fraction_sub(R.carrier, monoid_powers(R.mul, R.one, f)), " +
			"            ring_localization(R.carrier, monoid_powers(R.mul, R.one, f))), " +
			"        λy:set(prod(A, A)). y, " +
			"        N, " +
			"        n).zero}",
	},
		"U is a universe for R, its carrier a set of A's members, which inject into it "+
			"(LeftFactorIntoPowerSet, CardLeSubset, CardLeTrans, PowerSetUniverse); for the "+
			"polynomials over R by PolynomialRingCotangentUniverse, for R[x]/(f·x − 1), an ideal "+
			"quotient of them (HypersurfaceKoszulQuotient, KoszulQuotientIdealQuotient), by "+
			"QuotientCotangentUniverse, and for the fractions, a localization of R at the powers of f "+
			"(ToFractionIsLocalization), by LocalizationCotangentUniverse. f·x − 1 is a polynomial "+
			"over R and no zero divisor (FxMinusOneRegular) and separable (FxMinusOneSeparable), so "+
			"EtaleHypersurfaceVanishes kills D_n(R[x]/(f·x − 1) / R, N') for every module N' over the "+
			"quotient. LocalizationIsomorphicQuotient gives a ring isomorphism h from the fractions "+
			"onto the quotient with h(a / 1) the class of the constant a; its inverse φ is a ring "+
			"isomorphism back carrying the class of the constant a to a / 1 (IsomorphismInverse), the "+
			"constants being a ring map into the quotient (HypersurfaceConstantHomomorphism). "+
			"CotangentIsomorphismInvariance at φ, the coefficients the fractions through the identity "+
			"(RingHomIdentity), then CotangentCoefficientRestriction along φ, carry the vanishing to "+
			"D_n(R_f/R, N), as in SimpleSeparableExtensionCotangentVanishes"),
})}
