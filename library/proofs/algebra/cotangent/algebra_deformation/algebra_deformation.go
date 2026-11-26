// algebra_deformation.go — square-zero extensions moved along maps, and
// the deformations of an algebra over a square-zero thickening. Over a
// tower R → S → T: the pullback of an extension of T along g is an
// extension of S, its sections are the lifts of g, and its class is the
// obstruction to lifting; the lifts, when there are any, are a torsor
// under the derivations. The pushout along a linear map is an extension
// whose class is the coefficient map's image. In the cohomology sequence
// of the tower the right map is the pullback, the left map is injective
// when R → S is onto, and an extension of S is a pullback exactly when
// the connecting map kills its class, the compatible classes a torsor
// under D^1(T/S, N). For a thickening R → R₀ with square-zero kernel J,
// an algebra T over R₀ and a map ι from J into a module M over T: R is an
// extension of R₀ by J, ξ is its class pushed along ι, a deformation is
// an extension of T whose pullback has class ξ, one exists exactly when
// ∂¹(ξ) = 0 in D^2(T/R₀, M), their classes are a torsor under
// D^1(T/R₀, M), and the automorphisms of one are the derivations of T
// over R₀ into M.

package algebra_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cohomology_one"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/flat_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements over a tower R → S → T
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The spelling of the statements about a pushout
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The spelling of the statements about deformations
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The pullback and the lifts of an algebra map
// ---------------------------------------------------------------------------

// PullbackIsExtension — the pullback of a square-zero extension E of T
// by N along an algebra map g from S to T over R is a square-zero
// extension of S by N, N read over S through g, and the second
// projection is a ring map from it to E's ring.
var PullbackIsExtension = pullbackIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "PullbackIsExtension",
	Key:  "prop_b4b6e13d3b86fd62",
	Reading: "The members are the pairs (s, e) with g(s) = p(e). g an algebra map over R " +
		"is load-bearing for the structure map: (f(a), E.structure(a)) is a member because " +
		"g(f(a)) = p(E.structure(a)). The first projection is onto because E's projection is, " +
		"and its kernel is the pairs (S.zero, i(n)), on which (s, e) acts as p(e) = g(s) does.",
	Deps: []registry.EntryLike{
		SquareZeroPullbackDef,
		square_zero_extension.SquareZeroExtension,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.RingKernelDef,
		comm_ring.CommRingOn,
		comm_ring.MulRightZeroOn,
		module.ModuleOn,
		functions.InjectiveOnDef,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"«overT»(E)",
		},
		Conclusion: "«overS»(square_zero_pullback(S, f, g, E)) ∧ " +
			"ring_homomorphism(square_zero_pullback(S, f, g, E).ring, E.ring, λz:prod(B, I). snd(z))",
	},
		"unfold SquareZeroPullbackDef: the operations are componentwise at pairs (Fst, Snd, PairEq) "+
			"and the carrier is closed under them, g and E's projection being ring maps (MapAdd, "+
			"MapMul, MapOne), so it is a commutative ring with both projections ring maps (CommRingOn). "+
			"Each clause of SquareZeroExtension is E's clause at the second component: the first "+
			"projection is onto as E's is; its kernel is the pairs (S.zero, e) with p(e) = g(S.zero) = "+
			"T.zero, the image of N (RingKernelDef); (s, e)(S.zero, i(n)) = (S.zero, i(p(e) • n)) with "+
			"p(e) = g(s) (MulRightZeroOn). N read over S through g is a module, g a ring map (ModuleOn)"),
})}

// PullbackSplitsIffLift — a section over R of the pullback along g is a
// lift of g to E: a section σ gives the lift y ↦ snd(σ(y)), and a lift s
// gives the section y ↦ (y, s(y)).
var PullbackSplitsIffLift = pullbackSplitsIffLiftThm{family.Add(registry.ProofEntry{
	Name: "PullbackSplitsIffLift",
	Key:  "prop_6a601df8428dbfca",
	Reading: "A section is a lift of the identity of S (square_zero_lift at " +
		"λy. y). A section's first component is the identity on S's carrier, so " +
		"the two constructions are inverse there. No universe and no class is read.",
	Deps: []registry.EntryLike{
		SquareZeroPullbackDef,
		PullbackIsExtension,
		square_zero_extension.SquareZeroLiftDef,
		ring_homomorphism.RingHomomorphism,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"square_zero_extension(R, T, λa:A. g(f(a)), N, E)",
		},
		Conclusion: "(∀σ:(B → prod(B, I)). " +
			"    square_zero_lift(R, S, f, λy:B. y, square_zero_pullback(S, f, g, E), σ) ⇒ " +
			"    square_zero_lift(R, S, f, g, E, λy:B. snd(σ(y)))) ∧ " +
			"(∀s:(B → I). " +
			"    square_zero_lift(R, S, f, g, E, s) ⇒ " +
			"    square_zero_lift(R, S, f, λy:B. y, square_zero_pullback(S, f, g, E), λy:B. (y, s(y))))",
	},
		"unfold SquareZeroLiftDef on both sides. σ is a ring map into the pullback and snd one "+
			"out of it (PullbackIsExtension), so snd ∘ σ is a ring map; it carries f(a) to "+
			"snd((f(a), E.structure(a))) = E.structure(a), and E.projection(snd(σ(y))) = "+
			"g(fst(σ(y))) = g(y) by the pullback's carrier (SquareZeroPullbackDef). Conversely (y, "+
			"s(y)) is a member, E.projection(s(y)) = g(y), the map is componentwise a ring map (Fst, "+
			"Snd, PairEq), it carries f(a) to (f(a), E.structure(a)), and its first component is y"),
})}

// SplitExtensionClassZero — in a universe for R and S, the split
// extension S ⋉ N is a square-zero extension of S by N with the section
// y ↦ (y, 0); an extension of S by N has a section over R exactly when
// its class in D^1(S/R, N) is zero, exactly when it is isomorphic to
// S ⋉ N.
var SplitExtensionClassZero = splitExtensionClassZeroThm{family.Add(registry.ProofEntry{
	Name: "SplitExtensionClassZero",
	Key:  "prop_2c36cd3dcfeeedb6",
	Reading: "The zero of D^1 is the set of coboundaries, the class of the zero cocycle. A " +
		"section σ makes σ ∘ ε a lift of the standard presentation that reads the zero conormal " +
		"map, σ(ε(x)) = σ(S.zero) on the kernel. The split extension is P ⋉_ε N at P = S and ε " +
		"the identity, with structure map a ↦ (f(a), 0) and projection the first component.",
	Deps: []registry.EntryLike{
		square_zero_extension.SplitSquareZeroRing,
		square_zero_extension.SplitSquareZeroDef,
		square_zero_extension.SquareZeroExtension,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.ExtractConormalDef,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_classification.ExtensionIsoIffSameClass,
		cohomology_one.ConormalClassDef,
		cohomology_one.ConormalToCocycleDef,
		standard_resolution.StandardEpsHom,
		cotangent_complex.CotangentCohomologyDef,
		chain_complex.CohomologyModuleDef,
		submodule.QuotientModuleDef,
		functions.InverseOnLeft,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "square_zero_extension(R, S, f, N, «split»(S, f, N)) ∧ " +
			"square_zero_lift(R, S, f, λy:B. y, «split»(S, f, N), λy:B. (y, N.zero)) ∧ " +
			"(∀E:square_zero_ops(A, B, C, D). " +
			"    square_zero_extension(R, S, f, N, E) ⇒ " +
			"    ((∃σ:(B → C). square_zero_lift(R, S, f, λy:B. y, E, σ)) ⇔ " +
			"        square_zero_class⟨U:U⟩(R, S, f, N, E) = " +
			"        cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).zero) ∧ " +
			"    ((∃φ:(prod(B, D) → C). square_zero_isomorphism(R, N, «split»(S, f, N), E, φ)) ⇔ " +
			"        square_zero_class⟨U:U⟩(R, S, f, N, E) = " +
			"        cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).zero))",
	},
		"S ⋉ N is a commutative ring with (y, n) ↦ y a ring map and y ↦ (y, 0) a section "+
			"(SplitSquareZeroRing at P = S), and the clauses of SquareZeroExtension hold at the pairs "+
			"(S.zero, n). A section σ gives the lift σ ∘ ε of the standard presentation (StandardEpsHom, "+
			"SquareZeroLiftDef), whose conormal map is N.zero everywhere (ExtractConormalDef, "+
			"InverseOnLeft at the injective inclusion), so the class is the coset of the zero cochain, "+
			"the zero of D^1 (ExtensionClassWellDefined, ConormalClassDef, ConormalToCocycleDef, "+
			"CotangentCohomologyDef, CohomologyModuleDef, QuotientModuleDef). Class zero gives an "+
			"isomorphism from S ⋉ N, whose class is zero by its section (ExtensionIsoIffSameClass); an "+
			"isomorphism φ gives the section φ ∘ (y ↦ (y, 0)) (SquareZeroIsomorphismDef), and isomorphic "+
			"extensions have one class (ExtensionClassWellDefined)"),
})}

// LiftExistsIffObstructionZero — in a universe for R and S, an algebra
// map g from S to T over R lifts to a square-zero extension E of T by N
// exactly when the class of the pullback of E along g is zero in
// D^1(S/R, N).
var LiftExistsIffObstructionZero = liftExistsIffObstructionZeroThm{family.Add(registry.ProofEntry{
	Name: "LiftExistsIffObstructionZero",
	Key:  "prop_48e9ca185dc23481",
	Reading: "The class of the pullback is the obstruction to lifting g; no constant " +
		"names it. T needs no universe: only S's standard presentation is read. N is " +
		"read over S through g, so the class lives in D^1(S/R, N) with N over S.",
	Deps: []registry.EntryLike{PullbackIsExtension, PullbackSplitsIffLift, SplitExtensionClassZero},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"«overT»(E)",
		},
		Conclusion: "(∃s:(B → I). «liftOfG»(E, s)) ⇔ " +
			"square_zero_class⟨U:U⟩(R, S, f, scalar_restriction(g, N), square_zero_pullback(S, f, g, E)) = " +
			"cotangent_cohomology(R, S, f, S, λy:B. y, scalar_restriction(g, N), 1).zero",
	},
		"the pullback is an extension of S by N over R (PullbackIsExtension); its "+
			"sections over R are the lifts of g (PullbackSplitsIffLift), and an extension "+
			"has a section over R exactly when its class is zero (SplitExtensionClassZero)"),
})}

// LiftsTorsorUnderDerivations — the lifts of an algebra map g from S to
// T over R to a square-zero extension E of T by N, when there are any,
// are a torsor under the derivations of S over R into N: a derivation d
// moves a lift s to s + i ∘ d, two lifts differ by one derivation, and
// the derivation is determined on S's carrier.
var LiftsTorsorUnderDerivations = liftsTorsorUnderDerivationsThm{family.Add(registry.ProofEntry{
	Name: "LiftsTorsorUnderDerivations",
	Key:  "prop_edaa21fe07783b1",
	Reading: "The derivations are those of S over R into N with S acting through g, " +
		"Der_R(S, N), the group D^0(S/R, N) computes. The set of lifts may be empty " +
		"(LiftExistsIffObstructionZero). The Leibniz rule keeps s + i ∘ d multiplicative: " +
		"the cross term i(d(y))i(d(y')) vanishes and s(y)i(d(y')) is i(g(y) • d(y')).",
	Deps: []registry.EntryLike{
		square_zero_extension.LiftDifferenceDerivation,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.InclusionAdd,
		square_zero_extension.InclusionSquareZero,
		square_zero_extension.InclusionAction,
		partial_derivative.DerivationOn,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		comm_ring.SubAddNegOn,
		comm_ring.LeftDistribOn,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"«overT»(E)",
		},
		Conclusion: "(∀s:(B → I). ∀d:(B → D). " +
			"    «liftOfG»(E, s) ∧ «derivationOfS»(d) ⇒ " +
			"    «liftOfG»(E, λy:B. E.ring.add(s(y), E.inclusion(d(y))))) ∧ " +
			"(∀s s':(B → I). " +
			"    «liftOfG»(E, s) ∧ «liftOfG»(E, s') ⇒ " +
			"    ∃d:(B → D). " +
			"        «derivationOfS»(d) ∧ " +
			"        (∀y:B. y ∈ S.carrier ⇒ s'(y) = E.ring.add(s(y), E.inclusion(d(y))))) ∧ " +
			"(∀s:(B → I). ∀d d':(B → D). " +
			"    «liftOfG»(E, s) ∧ " +
			"    «derivationOfS»(d) ∧ " +
			"    «derivationOfS»(d') ∧ " +
			"    (∀y:B. " +
			"        y ∈ S.carrier ⇒ " +
			"        E.ring.add(s(y), E.inclusion(d(y))) = E.ring.add(s(y), E.inclusion(d'(y)))) ⇒ " +
			"    ∀y:B. y ∈ S.carrier ⇒ d(y) = d'(y))",
		Abbrev: Abbrev{
			{Name: "derivationOfS", Text: "derivation_on(R, S, f, scalar_restriction(g, N))"},
		},
	},
		"s + i ∘ d keeps sums (MapAdd, InclusionAdd), products (MapMul, the Leibniz rule of "+
			"DerivationOn, InclusionSquareZero, InclusionAction, LeftDistribOn) and one, d(S.one) being "+
			"N.zero; it carries f(a) to E.structure(a), d vanishing on f(a), and the projection kills "+
			"i(d(y)), so it lifts g (SquareZeroLiftDef). Transitivity is LiftDifferenceDerivation at P = "+
			"S, h = f, ε = g, its difference s' − s = i ∘ d rewritten s' = s + i ∘ d (SubAddNegOn). "+
			"Freeness: cancel s(y) and use the injectivity of the inclusion on N's carrier (InjectiveOnDef)"),
})}

// ---------------------------------------------------------------------------
// The pushout along a linear map
// ---------------------------------------------------------------------------

// PushoutIsExtension — for a square-zero extension E of S by N over R and
// a linear map ι from N to N' over S, the pushout ι_*E is a square-zero
// extension of S by N' over R; e ↦ [(e, 0)] is a ring map from E's ring,
// the projection reads [(e, m)] as p(e), and [(i(n), 0)] is the inclusion
// of ι(n).
var PushoutIsExtension = pushoutIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "PushoutIsExtension",
	Key:  "prop_326fd3593657d5fb",
	Reading: "The relations (i(n), −ι(n)) are an ideal of E.ring ⋉ N' because i(n) has " +
		"projection S.zero and so acts on N' by zero, and because ι is linear over S. The " +
		"last conjunct, [(i(n), 0)] = [(0, ι(n))], is how the pushout carries E's kernel " +
		"along ι; with the ring map e ↦ [(e, 0)] it is the map of extensions E → ι_*E over ι.",
	Deps: []registry.EntryLike{
		SquareZeroPushoutDef,
		square_zero_extension.SquareZeroExtension,
		square_zero_extension.ProjectionHomomorphism,
		square_zero_extension.InclusionAction,
		square_zero_extension.SplitSquareZeroRing,
		square_zero_extension.SplitSquareZeroDef,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.IdealQuotientRingDef,
		quotient_ring.IdealQuotientProjectionDef,
		quotient_ring.CosetEqIff,
		quotient_ring.QuotientMulCoset,
		equivalence.InducedMapDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
		ring_ideal.RingIdealDef,
		functions.InjectiveOnDef,
		set_basic.InImage,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, F). " +
			"∀N':module_ops(B, D). " +
			"∀ι:(F → D). " +
			"∀E:square_zero_ops(A, B, I, F).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"module_homomorphism(S, N, N', ι)",
		},
		Conclusion: "square_zero_extension(R, S, f, N', square_zero_pushout(N, N', ι, E)) ∧ " +
			"ring_homomorphism(E.ring, " +
			"    square_zero_pushout(N, N', ι, E).ring, " +
			"    λe:I. " +
			"        ideal_quotient_projection(split_square_zero(E.ring, E.projection, N'), " +
			"            image(λn:F. (E.inclusion(n), N'.neg(ι(n))), N.carrier), " +
			"            (e, N'.zero))) ∧ " +
			"(∀e:I. ∀m:D. " +
			"    e ∈ E.ring.carrier ∧ m ∈ N'.carrier ⇒ " +
			"    square_zero_pushout(N, N', ι, E).projection(ideal_quotient_projection( " +
			"            split_square_zero(E.ring, E.projection, N'), " +
			"            image(λn:F. (E.inclusion(n), N'.neg(ι(n))), N.carrier), " +
			"            (e, m))) = " +
			"    E.projection(e)) ∧ " +
			"(∀n:F. " +
			"    n ∈ N.carrier ⇒ " +
			"    ideal_quotient_projection(split_square_zero(E.ring, E.projection, N'), " +
			"        image(λn:F. (E.inclusion(n), N'.neg(ι(n))), N.carrier), " +
			"        (E.inclusion(n), N'.zero)) = " +
			"    square_zero_pushout(N, N', ι, E).inclusion(ι(n)))",
	},
		"E.ring ⋉ N' at ε = E.projection is a commutative ring (SplitSquareZeroRing, the "+
			"projection a ring map by ProjectionHomomorphism). The relations are an ideal "+
			"(RingIdealDef): they hold the zero pair, are closed under sums, and (e, m)(i(n), −ι(n)) "+
			"= (i(p(e) • n), −ι(p(e) • n)) by InclusionAction, p(i(n)) = S.zero and HomSmul. The "+
			"quotient is a ring and the coset map a ring map (IdealQuotientProjection); [(e, m)] ↦ "+
			"p(e) is well defined, two members of a coset differing by some (i(n), −ι(n)) "+
			"(CosetEqIff, InducedMapDef). m ↦ [(0, m)] is additive and injective, (0, m) a relation "+
			"forcing i(n) = E.ring.zero, n = N.zero and m = −ι(N.zero) = N'.zero (HomZero); its image "+
			"is the kernel, [(e, m)] with p(e) = S.zero being [(i(n), m)] = [(0, m + ι(n))]; [(e, "+
			"m)][(0, m')] = [(0, p(e) • m')] gives the action and the square zero (QuotientMulCoset)"),
})}

// PushoutClassIsCoefficientMap — in a universe for R and S, the class of
// the pushout ι_*E in D^1(S/R, N') is the image of the class of E under
// the map composition with ι induces on cohomology.
var PushoutClassIsCoefficientMap = pushoutClassIsCoefficientMapThm{family.Add(registry.ProofEntry{
	Name: "PushoutClassIsCoefficientMap",
	Key:  "prop_9e62af030aedd1ec",
	Reading: "The coefficient map is composition with ι on the cochains, cohomology_map " +
		"sending the coset of a cocycle c to the coset of ι ∘ c. A lift s of the standard " +
		"presentation to E gives the lift u ↦ [(s(u), 0)] to the pushout, whose conormal " +
		"map is ι ∘ γ_s on the kernel; ι keeps the zero, so the two agree off it too.",
	Deps: []registry.EntryLike{
		PushoutIsExtension,
		square_zero_classification.StandardExtensionLiftExists,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.ExtractConormalDef,
		cohomology_one.ConormalToCocycleDef,
		cohomology_one.ConormalClassDef,
		cotangent_complex.CotangentCochainDef,
		cotangent_complex.CotangentCochainComplex,
		chain_complex.CohomologyMapDef,
		chain_complex.CoboundariesDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, F). " +
			"∀N':module_ops(B, D). " +
			"∀ι:(F → D). " +
			"∀E:square_zero_ops(A, B, I, F).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"square_zero_extension(R, S, f, N, E)",
			"module_homomorphism(S, N, N', ι)",
		},
		Conclusion: "square_zero_class⟨U:U⟩(R, S, f, N', «pushout») = " +
			"cohomology_map(cotangent_cochain(R, S, f, S, λy:B. y, N'), " +
			"    λk:num. λw:(U → F). λu:U. ι(w(u)), " +
			"    1, " +
			"    square_zero_class(R, S, f, N, E))",
		Abbrev: Abbrev{
			{Name: "pushout", Text: "square_zero_pushout(N, N', ι, E)"},
		},
	},
		"let s be a lift of the standard presentation's augmentation to E "+
			"(StandardExtensionLiftExists); u ↦ [(s(u), 0)] is a lift to the pushout, the coset map being a "+
			"ring map over R and over S (PushoutIsExtension, SquareZeroLiftDef). On the kernel s(x) = "+
			"i(γ_s(x)), so [(s(x), 0)] = [(0, ι(γ_s(x)))] (PushoutIsExtension's last conjunct) and the lift "+
			"reads ι ∘ γ_s (ExtractConormalDef, InjectiveOnDef); off the kernel both are N'.zero (HomZero). "+
			"So the pushout's class is the coset of C(ι ∘ γ_s) = ι ∘ C(γ_s) (ExtensionClassWellDefined, "+
			"ConormalToCocycleDef, ConormalClassDef). Composition with ι carries the coboundaries of N into "+
			"those of N', the transposed Jacobians being finite sums of scalars acting (HomSum, HomSmul, "+
			"CotangentCochainDef, CotangentCochainComplex), so cohomology_map at the coset of C(γ_s) is the "+
			"coset of ι ∘ C(γ_s) (CohomologyMapDef, CoboundariesDef)"),
})}

// ---------------------------------------------------------------------------
// The cohomology sequence of the tower
// ---------------------------------------------------------------------------

// CohomologyCoefficientRestriction — for a ring map k from T to T' and a
// module N' over T', the cohomology of S over R with coefficients in N'
// through k after g has the classes, the zero and the sum of the
// cohomology with coefficients in N' read over T along k.
var CohomologyCoefficientRestriction = cohomologyCoefficientRestrictionThm{family.Add(registry.ProofEntry{
	Name: "CohomologyCoefficientRestriction",
	Key:  "prop_e84aa40dcb383104",
	Reading: "No hypothesis on R, S, f or g and no universe: the two cochain complexes " +
		"have the same terms, the same sum and the same coboundary, t in T acting on N as " +
		"k(t) acts on N'. Only the scalars of the two modules differ. It is the cochain side " +
		"of CotangentCoefficientRestriction, and it is how a class computed over S itself, " +
		"the coefficients read over S through g, is a class of D^n(S/R, N) with N over T.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentCoefficientRestriction,
		cotangent_complex.CotangentCohomologyDef,
		cotangent_complex.CotangentCochainDef,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesDef,
		chain_complex.ComplexModuleDef,
		submodule.QuotientModuleDef,
		module_record.RestrictModuleDef,
		function_module.FunModuleDef,
		partial_derivative.FreeAlgebraJacobianTransposeDef,
		comm_ring.AlternatingSignDef,
		ring_homomorphism.MapOne,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀T':ring_ops(E). " +
			"∀k:(C → E). " +
			"∀N':module_ops(E, D).",
		Hypotheses: []string{
			"ring_homomorphism(T, T', k)",
			"module_on(T', N')",
			"N = scalar_restriction(k, N')",
		},
		Conclusion: "module_on(T, N) ∧ " +
			"(∀n:num. " +
			"    cotangent_cohomology⟨U:U⟩(R, S, f, T', λy:B. k(g(y)), N', n).carrier = " +
			"    cotangent_cohomology(R, S, f, T, g, N, n).carrier ∧ " +
			"    cotangent_cohomology⟨U:U⟩(R, S, f, T', λy:B. k(g(y)), N', n).zero = " +
			"    cotangent_cohomology(R, S, f, T, g, N, n).zero ∧ " +
			"    cotangent_cohomology⟨U:U⟩(R, S, f, T', λy:B. k(g(y)), N', n).add = " +
			"    cotangent_cohomology(R, S, f, T, g, N, n).add)",
	},
		"unfold both cohomologies to the cochain complexes (CotangentCohomologyDef, "+
			"CohomologyModuleDef, CotangentCochainDef): the terms are the functions into N'.carrier "+
			"vanishing off the names, under the pointwise operations of N' (FunModuleDef). The coboundary "+
			"scales by alternating_sign(i), which k carries to alternating_sign(i) (AlternatingSignDef, "+
			"MapOne, AdditiveHomomorphism), and each transposed Jacobian with entries g(…) scaled in N is "+
			"the one with entries k(g(…)) scaled in N' (FreeAlgebraJacobianTransposeDef). So the cocycles "+
			"and the coboundaries are equal sets (CocyclesDef, CoboundariesDef), and the cohomology "+
			"modules have the same cosets, zero and sum (QuotientModuleDef, RestrictModuleDef, "+
			"ComplexModuleDef). N is a module over T as in CotangentCoefficientRestriction"),
})}

// SurjectiveBaseDerivationsZero — in a universe for R and S, when f maps
// R onto S, D^0(S/R, N) is zero for every module N over T.
var SurjectiveBaseDerivationsZero = surjectiveBaseDerivationsZeroThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveBaseDerivationsZero",
	Key:  "prop_8ac4d95dc6937302",
	Reading: "D^0 is the 0-cocycles themselves, the functions h on the tags of S's " +
		"elements whose coboundary vanishes; at the constant polynomial of a the " +
		"coboundary is −h(tag f(a)), so h vanishes on every tag when f is onto. Without " +
		"onto, D^0(S/R, N) is the derivations of S over R into N, which need not vanish.",
	Deps: []registry.EntryLike{
		cohomology_one.CotangentLowCoboundaries,
		CohomologyCoefficientRestriction,
		partial_derivative.FreeAlgebraDerivationFromValues,
		standard_resolution.StandardLowFaceFormulas,
		standard_resolution.StandardEpsHom,
		function_module.FunModuleDef,
		cotangent_complex.CotangentCohomologyDef,
		chain_complex.CohomologyModuleDef,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"image(f, R.carrier) = S.carrier",
			"module_on(T, N)",
		},
		Conclusion: "cotangent_cohomology⟨U:U⟩(R, S, f, T, g, N, 0).carrier = {«cohomologySR»(0).zero}",
		Abbrev: Abbrev{
			{Name: "cohomologySR", Text: "cotangent_cohomology(R, S, f, T, g, N)"},
		},
	},
		"the coboundary of a 0-cochain h at u in P = R[S] is D_h(u) − D_h(τ(u)) "+
			"(CotangentLowCoboundaries, with the coefficients read over S through "+
			"CohomologyCoefficientRestriction); at the constant of a, D_h vanishes "+
			"(FreeAlgebraDerivationFromValues) and τ is the variable of the tag of f(a) "+
			"(StandardLowFaceFormulas, StandardEpsHom), so a cocycle has h(tag f(a)) = N.zero. f "+
			"onto makes every tag of S's carrier such a tag, and a cochain is N.zero off the tags "+
			"(FunModuleDef): the zero function is the only cocycle, and D^0 is its one class, the "+
			"zero (CotangentCohomologyDef, CohomologyModuleDef, CocyclesDef, CoboundariesDef)"),
})}

// RestrictionMapInjective — in a universe for the three rings, when f
// maps R onto S, the map D^1(T/S, N) → D^1(T/R, N) of the cohomology
// sequence is injective.
var RestrictionMapInjective = restrictionMapInjectiveThm{family.Add(registry.ProofEntry{
	Name: "RestrictionMapInjective",
	Key:  "prop_9e1c2db890ca8ba8",
	Reading: "The sequence reads D^0(S/R, N) → D^1(T/S, N) → D^1(T/R, N), and its " +
		"first term vanishes when f is onto: an extension of T over S is determined " +
		"by the extension over R it is. Without onto, the connecting image of a " +
		"derivation of S over R is a nonzero class over S that vanishes over R.",
	Deps: []registry.EntryLike{
		SurjectiveBaseDerivationsZero,
		transitivity.CotangentCohomologyTransitivity,
		transitivity.CoTransitivityLeftMapDef,
		chain_complex.CohomologyMapHom,
		cotangent_complex.CotangentMapsDualAgreement,
		module_homomorphism.KernelTrivialIffInjective,
		module_homomorphism.ExactAtDef,
		group_homomorphism.GroupKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"image(f, R.carrier) = S.carrier",
			"module_on(T, N)",
		},
		Conclusion: "injective_on(«cohomologyTS»(1).carrier, " +
			"    co_transitivity_left_map(R, S, f, T, g, N, 1))",
	},
		"exactness at D^1(T/S, N) (CotangentCohomologyTransitivity, ExactAtDef, GroupKernelDef) "+
			"makes the kernel of the left map the image of the connecting map out of D^0(S/R, N), a "+
			"single class by SurjectiveBaseDerivationsZero. The left map is a homomorphism of the "+
			"cohomology modules, the map on cohomology of a cochain map (CoTransitivityLeftMapDef, "+
			"CotangentMapsDualAgreement, CohomologyMapHom), so the zero is in its kernel, the kernel is "+
			"the zero alone, and a homomorphism with zero kernel is injective (KernelTrivialIffInjective)"),
})}

// RightMapIsPullback — in a universe for the three rings, the map
// D^1(T/R, N) → D^1(S/R, N) of the cohomology sequence carries the class
// of a square-zero extension E of T by N to the class of its pullback
// along g.
var RightMapIsPullback = rightMapIsPullbackThm{family.Add(registry.ProofEntry{
	Name: "RightMapIsPullback",
	Key:  "prop_e68fe4ae4e7be123",
	Reading: "Both sides are cosets of one set of coboundaries: the right map lands in " +
		"D^1(S/R, N) with N over T, the pullback's class in D^1(S/R, N) with N read over " +
		"S, which have the same classes (CohomologyCoefficientRestriction). In degree 1 " +
		"the right map is precomposition with the map R[S] → R[T] that g induces on the " +
		"tags; it carries τ_S(u) to τ_T of the image, which is why the two cochains agree.",
	Deps: []registry.EntryLike{
		PullbackIsExtension,
		CohomologyCoefficientRestriction,
		transitivity.CoTransitivityRightMapDef,
		standard_resolution.StandardMapDef,
		standard_resolution.StandardMapAugmentation,
		standard_resolution.StandardRepresentativeDef,
		partial_derivative.PartialVar,
		partial_derivative.FreeAlgebraJacobianTransposeDef,
		square_zero_classification.StandardExtensionLiftExists,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.ExtractConormalDef,
		cohomology_one.ConormalToCocycleDef,
		cohomology_one.ConormalClassDef,
		chain_complex.CohomologyMapDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"«overT»(E)",
		},
		Conclusion: "«rightMap»(«classT»(E)) = " +
			"square_zero_class⟨U:U⟩(R, S, f, scalar_restriction(g, N), square_zero_pullback(S, f, g, E))",
	},
		"in degree 1 the transposed Jacobian of standard_map(R, S, T, g) sends a 1-cochain w to w ∘ Φ, "+
			"Φ = standard_map(R, S, T, g, 0), each variable going to a variable (CoTransitivityRightMapDef, "+
			"StandardMapDef, PartialVar, FreeAlgebraJacobianTransposeDef). For a lift s of T's presentation "+
			"to E (StandardExtensionLiftExists), u ↦ (ε_S(u), s(Φ(u))) is a lift of S's presentation to the "+
			"pullback, Φ covering g (StandardMapAugmentation, PullbackIsExtension, SquareZeroLiftDef), and "+
			"it reads γ_s ∘ Φ on the kernel (ExtractConormalDef). Φ carries τ_S(u) to τ_T(Φ(u)), both the "+
			"variable of the tag of g(ε_S(u)) (StandardRepresentativeDef), so C_S(γ_s ∘ Φ) = C_T(γ_s) ∘ Φ "+
			"(ConormalToCocycleDef); both sides are the coset of that cochain (ExtensionClassWellDefined, "+
			"ConormalClassDef, CohomologyMapDef, CohomologyCoefficientRestriction)"),
})}

// TowerExtensionObstruction — in a universe for the three rings, a
// square-zero extension S' of S by N over R is the pullback along g of an
// extension of T by N over R exactly when the connecting map sends its
// class to zero in D^2(T/S, N).
var TowerExtensionObstruction = towerExtensionObstructionThm{family.Add(registry.ProofEntry{
	Name: "TowerExtensionObstruction",
	Key:  "prop_62beed2efca6aaf",
	Reading: "The extension asked for exists at set(prod(U, D)), the type of the realizations, " +
		"where every class of D^1(T/R, N) has one; a type too small for T's carrier has none, so " +
		"the converse is stated at every type. The class of S' is read in D^1(S/R, N) with N over " +
		"S, the classes of the sequence's D^1(S/R, N) (CohomologyCoefficientRestriction).",
	Deps: []registry.EntryLike{
		RightMapIsPullback,
		PullbackIsExtension,
		CohomologyCoefficientRestriction,
		transitivity.CotangentCohomologyTransitivity,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_classification.ExtensionIsoIffSameClass,
		square_zero_classification.SquareZeroRealizationDef,
		module_homomorphism.ExactAtDef,
		group_homomorphism.GroupKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀S':square_zero_ops(A, B, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"«overS»(S')",
		},
		Conclusion: "(∀T':square_zero_ops(A, C, F, D). ∀φ:(I → prod(B, F)). " +
			"    «overT»(T') ∧ " +
			"    square_zero_isomorphism(R, " +
			"        scalar_restriction(g, N), " +
			"        S', " +
			"        square_zero_pullback(S, f, g, T'), " +
			"        φ) ⇒ " +
			"    «connecting»(«classS»(S')) = «cohomologyTS»(2).zero) ∧ " +
			"(«connecting»(«classS»(S')) = «cohomologyTS»(2).zero ⇒ " +
			"    ∃T':square_zero_ops(A, C, set(prod(U, D)), D). ∃φ:(I → prod(B, set(prod(U, D)))). " +
			"        «overT»(T') ∧ " +
			"        square_zero_isomorphism(R, " +
			"            scalar_restriction(g, N), " +
			"            S', " +
			"            square_zero_pullback(S, f, g, T'), " +
			"            φ))",
		Abbrev: Abbrev{
			{Name: "connecting", Text: "co_transitivity_connecting(R, S, f, T, g, N, 1)"},
		},
	},
		"⇒: isomorphic extensions have one class (ExtensionClassWellDefined), so the class of S' is "+
			"the pullback's, the right map's image of the class of T' (RightMapIsPullback), and "+
			"exactness at D^1(S/R, N) (CotangentCohomologyTransitivity, ExactAtDef, GroupKernelDef) "+
			"puts it in the kernel of the connecting map. ⇐: by exactness the class of S' is the right "+
			"map's image of some c in D^1(T/R, N); its realization T' is an extension with class c "+
			"(ExtensionRealizeClass, SquareZeroRealizationDef), the class of its pullback is the class "+
			"of S' (RightMapIsPullback, CohomologyCoefficientRestriction), and ExtensionIsoIffSameClass "+
			"gives the isomorphism, the pullback being an extension of S (PullbackIsExtension)"),
})}

// TowerExtensionTorsor — in a universe for the three rings, with f onto
// S, the classes in D^1(T/R, N) that the right map sends to the class of
// an extension S' of S are a torsor under D^1(T/S, N): ζ ↦ ζ + i*(η) keeps
// them, and two of them differ by exactly one η.
var TowerExtensionTorsor = towerExtensionTorsorThm{family.Add(registry.ProofEntry{
	Name: "TowerExtensionTorsor",
	Key:  "prop_25470969c036221c",
	Reading: "By RightMapIsPullback and ExtensionIsoIffSameClass these are the " +
		"classes of the extensions of T by N over R whose pullback along g is isomorphic " +
		"to S'; the set may be empty (TowerExtensionObstruction). The action is the left " +
		"map followed by the sum of D^1(T/R, N). Freeness is RestrictionMapInjective and " +
		"needs f onto; without it the classes are a torsor under the left map's image only.",
	Deps: []registry.EntryLike{
		RestrictionMapInjective,
		transitivity.CotangentCohomologyTransitivity,
		transitivity.CoTransitivityRightMapDef,
		transitivity.CoTransitivityLeftMapDef,
		chain_complex.CohomologyMapHom,
		cotangent_complex.CotangentMapsDualAgreement,
		cotangent_complex.CotangentCohomologyModuleOn,
		module.AddGroupOn,
		module_homomorphism.ExactAtDef,
		group_homomorphism.GroupKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀S':square_zero_ops(A, B, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"image(f, R.carrier) = S.carrier",
			"module_on(T, N)",
			"«overS»(S')",
		},
		Conclusion: "(∀ζ η:set(U → D). " +
			"    ζ ∈ «cohomologyTR»(1).carrier ∧ " +
			"    «rightMap»(ζ) = «classS»(S') ∧ " +
			"    η ∈ «cohomologyTS»(1).carrier ⇒ " +
			"    «rightMap»(«cohomologyTR»(1).add(ζ, «leftMap»(η))) = «classS»(S')) ∧ " +
			"(∀ζ ζ':set(U → D). " +
			"    ζ ∈ «cohomologyTR»(1).carrier ∧ " +
			"    ζ' ∈ «cohomologyTR»(1).carrier ∧ " +
			"    «rightMap»(ζ) = «classS»(S') ∧ " +
			"    «rightMap»(ζ') = «classS»(S') ⇒ " +
			"    ∃η:set(U → D). " +
			"        η ∈ «cohomologyTS»(1).carrier ∧ " +
			"        ζ' = «cohomologyTR»(1).add(ζ, «leftMap»(η)) ∧ " +
			"        (∀η':set(U → D). " +
			"            η' ∈ «cohomologyTS»(1).carrier ∧ ζ' = «cohomologyTR»(1).add(ζ, «leftMap»(η')) ⇒ " +
			"            η' = η))",
		Abbrev: Abbrev{
			{Name: "cohomologyTR", Text: "cotangent_cohomology(R, T, λa:A. g(f(a)), T, λc:C. c, N)"},
		},
	},
		"the right and the left map are homomorphisms of the cohomology modules "+
			"(CoTransitivityRightMapDef, CoTransitivityLeftMapDef, CotangentMapsDualAgreement, "+
			"CohomologyMapHom), and the right map kills the left map's image (exactness at "+
			"D^1(T/R, N), CotangentCohomologyTransitivity, ExactAtDef, GroupKernelDef), so the "+
			"right map of ζ + i*(η) is the class of S' plus the zero. Two such classes differ "+
			"by a member of the right map's kernel, the left map's image by exactness, so ζ' = "+
			"ζ + i*(η); η is unique since the left map is injective (RestrictionMapInjective) "+
			"and D^1(T/R, N) is a group (CotangentCohomologyModuleOn, AddGroupOn)"),
})}

// ---------------------------------------------------------------------------
// The thickening and its class
// ---------------------------------------------------------------------------

// ThickeningIsExtension — a ring map f from R onto R₀ whose kernel J has
// square zero makes J a module over R₀, a member of R₀ acting through any
// preimage, and makes R, with the identity as structure map, the
// inclusion of J and f as projection, a square-zero extension of R₀ by J
// over R.
var ThickeningIsExtension = thickeningIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "ThickeningIsExtension",
	Key:  "prop_a141c389b7c4ee38",
	Reading: "The square-zero hypothesis is load-bearing twice: it makes the action " +
		"of R₀ on J independent of the preimage chosen, two preimages differing by a " +
		"member of J, which kills J; and it is the square-zero clause of the extension. " +
		"f onto lets every member of R₀ act. R₀ = R/J with its projection is one such " +
		"thickening, and so is the first projection of split_square_zero(P, λx. x, N).",
	Deps: []registry.EntryLike{
		ThickeningKernelDef,
		square_zero_extension.SquareZeroExtension,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.RingHomIdentity,
		module.ModuleOn,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
		comm_ring.SubAddNegOn,
		comm_ring.LeftDistribOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀R₀:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
		},
		Conclusion: "module_on(R₀, thickening_kernel(R, R₀, f)) ∧ " +
			"square_zero_extension(R, R₀, f, thickening_kernel(R, R₀, f), «thickening»)",
		Abbrev: Abbrev{
			{Name: "thickening", Text: "mk_square_zero(R, λa:A. a, λj:A. j, f)"},
		},
	},
		"J is an ideal (KernelIdeal), so an additive subgroup of R closed under multiplication by R's "+
			"carrier. The chosen preimage of b lies in R's carrier over b (InverseOnIn, InverseOnRight, f "+
			"onto), and two preimages of one member differ by a member of J, so their products with j "+
			"agree by the square-zero hypothesis (SubAddNegOn, LeftDistribOn): this gives the module "+
			"laws, one acting as R.one does (ModuleOn, ThickeningKernelDef). The extension: the identity "+
			"is a ring map (RingHomIdentity), f one onto R₀, the inclusion of J additive and injective "+
			"with image the kernel, J of square zero, and e j = b j for b the chosen preimage of f(e), e "+
			"− b lying in J (SquareZeroExtension, RingKernelDef, InjectiveOnDef)"),
})}

// ---------------------------------------------------------------------------
// Deformations
// ---------------------------------------------------------------------------

// DeformationIffPullbackClass — in a universe for the three rings, a
// square-zero extension E of T by M over R is a deformation exactly when
// the class of its pullback along g is the thickening class ξ; then
// (a, m) ↦ (f(a), E.structure(a) + i(m)) induces an isomorphism from the
// thickening pushed along ι onto the pullback.
var DeformationIffPullbackClass = deformationIffPullbackClassThm{family.Add(registry.ProofEntry{
	Name: "DeformationIffPullbackClass",
	Key:  "prop_33071e93dd42bc2a",
	Reading: "f*[E] = ξ is the deformation condition read in D^1(R₀/R, M); the definition reads " +
		"it on J, the structure map agreeing there with the inclusion after ι. The isomorphism is " +
		"the one the equality of classes promises, written out: a relation (j, −ι(j)) goes to " +
		"(S.zero, E.structure(j) − i(ι(j))), which vanishes exactly for a deformation.",
	Deps: []registry.EntryLike{
		ThickeningClassDef,
		AlgebraDeformationDef,
		ThickeningIsExtension,
		PushoutIsExtension,
		PullbackIsExtension,
		SquareZeroPushoutDef,
		SquareZeroPullbackDef,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_classification.ExtensionIsoIffSameClass,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SplitSquareZeroDef,
		quotient_ring.QuotientFirstIso,
		equivalence.InducedMapDef,
		ring_homomorphism.RingKernelDef,
		functions.InjectiveOnDef,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
			"square_zero_extension(R, T, λa:A. g(f(a)), M, E)",
		},
		Conclusion: "(algebra_deformation(R, R₀, f, T, g, M, ι, E) ⇔ " +
			"    square_zero_class⟨U:U⟩(R, " +
			"        R₀, " +
			"        f, " +
			"        scalar_restriction(g, M), " +
			"        square_zero_pullback(R₀, f, g, E)) = " +
			"    thickening_class(R, R₀, f, scalar_restriction(g, M), ι)) ∧ " +
			"(algebra_deformation(R, R₀, f, T, g, M, ι, E) ⇒ " +
			"    square_zero_isomorphism(R, " +
			"        scalar_restriction(g, M), " +
			"        square_zero_pushout(thickening_kernel(R, R₀, f), " +
			"            scalar_restriction(g, M), " +
			"            ι, " +
			"            mk_square_zero(R, λa:A. a, λj:A. j, f)), " +
			"        square_zero_pullback(R₀, f, g, E), " +
			"        induced_map( " +
			"            λz:prod(A, D). (f(fst(z)), E.ring.add(E.structure(fst(z)), E.inclusion(snd(z)))))))",
	},
		"⇒ and the isomorphism: (a, m) ↦ (f(a), k(a) + i(m)) is a ring map from R ⋉ M onto the "+
			"pullback (SplitSquareZeroDef, PullbackIsExtension) whose kernel is the relations (j, "+
			"−ι(j)): f(a) = R₀.zero puts a in J, and then k(a) = i(ι(a)) (AlgebraDeformationDef, "+
			"RingKernelDef, InjectiveOnDef). So the induced map is a ring isomorphism "+
			"(QuotientFirstIso, InducedMapDef, SquareZeroPushoutDef), over R, the identity on M and "+
			"over R₀ (SquareZeroIsomorphismDef, SquareZeroPullbackDef), and the classes agree "+
			"(ExtensionClassWellDefined, ThickeningClassDef). ⇐: equal classes give an isomorphism φ "+
			"from the pushed thickening onto the pullback (ExtensionIsoIffSameClass, "+
			"ThickeningIsExtension, PushoutIsExtension); φ carries [(j, 0)] = [(0, ι(j))] to (R₀.zero, "+
			"k(j)) as the structure map and to (R₀.zero, i(ι(j))) as the inclusion, so k(j) = i(ι(j))"),
})}

// DeformationKernelGenerated — for a deformation E, when ι(J) spans M over
// T, the kernel of the projection of E is the ideal J·E that the
// structure map's image of J generates.
var DeformationKernelGenerated = deformationKernelGeneratedThm{family.Add(registry.ProofEntry{
	Name: "DeformationKernelGenerated",
	Key:  "prop_21eff0c28afbab3c",
	Reading: "The spanning hypothesis is load-bearing: J·E is the inclusion of " +
		"the span of ι(J) over T, so it is the whole kernel exactly when that span " +
		"is M. It holds for M = J ⊗_{R₀} T with ι(j) = j ⊗ 1, the case of a flat " +
		"deformation; with ι = 0 and M nonzero, J·E is zero and the kernel is not.",
	Deps: []registry.EntryLike{
		AlgebraDeformationDef,
		square_zero_extension.InclusionAdd,
		square_zero_extension.InclusionAction,
		square_zero_extension.ProjectionOnto,
		square_zero_extension.InclusionImage,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanLeast,
		ring_ideal.SpanContains,
		ring_ideal.SpanIdeal,
		submodule.ModuleSpanDef,
		submodule.SpanLeast,
		submodule.SubmoduleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
			"algebra_deformation(R, R₀, f, T, g, M, ι, E)",
			"module_span(T, M, image(ι, ring_kernel(R₀.zero, R.carrier, f))) = M.carrier",
		},
		Conclusion: "ring_kernel(T.zero, E.ring.carrier, E.projection) = " +
			"ideal_span(E.ring, image(E.structure, ring_kernel(R₀.zero, R.carrier, f)))",
	},
		"the ideal is inside the kernel, an ideal (KernelIdeal) holding k(j), whose projection is "+
			"g(f(j)) = T.zero (ring_ideal.SpanLeast, RingKernelDef). Conversely the m of M with i(m) in the "+
			"ideal are a submodule over T: sums by additivity of i (InclusionAdd), and t • m with i(t • m) = "+
			"e i(m) for e over t (InclusionAction, ProjectionOnto, SpanIdeal); it holds ι(J), i(ι(j)) = k(j) "+
			"(AlgebraDeformationDef, SpanContains), so it holds the span, which is M (submodule.SpanLeast, "+
			"SubmoduleDef, ModuleSpanDef), and the kernel is the image of M (InclusionImage)"),
})}

// DeformationIffFlat — for J an ideal of square zero, T flat over R/J and
// M the base change T ⊗_{R/J} J through ι, an algebra X over R with a
// map p onto T over R is flat over R with kernel J·X exactly when some
// inclusion i of M makes (X, k, i, p) a deformation.
var DeformationIffFlat = deformationIffFlatThm{family.Add(registry.ProofEntry{
	Name: "DeformationIffFlat",
	Key:  "prop_313e3806c29f07a3",
	Reading: "T flat over R₀ is load-bearing for ⇐: over R = k[x][ε]/(ε²), R₀ = k[x], T = " +
		"k[x]/(x), the algebra X = R/(x) with i(1) = ε is a deformation and is not flat over R. The " +
		"inclusion is existential: over k[ε] → k with ι(ε) = 1, X = k[ε] with i(m) = −m ε is flat " +
		"with kernel J·X and is not a deformation for ι. No class is read and no universe is asked.",
	Deps: []registry.EntryLike{
		DeformationKernelGenerated,
		AlgebraDeformationDef,
		ThickeningIsExtension,
		square_zero_extension.SquareZeroExtension,
		tensor_product.TensorSpan,
		tensor_product.TensorUniversal,
		flat_module.FlatModuleDef,
		flat_module.IdealQuotientModuleDef,
		flat_module.SquareZeroFlatCriterion,
		flat_module.FlatIsomorphic,
		flat_module.SquareZeroFlatForward,
		flat_module.TensorSquareZeroBaseChange,
		module_homomorphism.FirstIsomorphism,
		module_homomorphism.IsomorphismInverse,
		flat_module.IdealQuotientModuleOn,
		tensor_product.TensorUniversalUnique,
		quotient_ring.CosetEqIdealIff,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀J:set(A). " +
			"∀T:ring_ops(C). " +
			"∀g:(set(A) → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"∀X:ring_ops(I). " +
			"∀k:(A → I). " +
			"∀p:(I → C).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"ring_homomorphism(R, ideal_quotient_ring(R, J), ideal_quotient_projection(R, J))",
			"∀x y:A. x ∈ J ∧ y ∈ J ⇒ R.mul(x, y) = R.zero",
			"ring_homomorphism(ideal_quotient_ring(R, J), T, g)",
			"module_on(T, M)",
			"module_homomorphism(ideal_quotient_ring(R, J), " +
				"    thickening_kernel(R, ideal_quotient_ring(R, J), ideal_quotient_projection(R, J)), " +
				"    scalar_restriction(g, M), " +
				"    ι)",
			"flat_module(ideal_quotient_ring(R, J), «tOverQuotient»)",
			"∃h:(set(prod(C, set(A)) → set(A)) → D). " +
				"    module_isomorphism(ideal_quotient_ring(R, J), " +
				"        tensor_module(ideal_quotient_ring(R, J), «tOverQuotient», «jOverQuotient»), " +
				"        scalar_restriction(g, M), " +
				"        h) ∧ " +
				"    (∀t:C. ∀j:A. " +
				"        t ∈ T.carrier ∧ j ∈ J ⇒ " +
				"        h(tensor(ideal_quotient_ring(R, J), «tOverQuotient», «jOverQuotient», t, {j})) = " +
				"        M.smul(t, ι(j)))",
			"ring_homomorphism(R, X, k)",
			"ring_homomorphism(X, T, p)",
			"image(p, X.carrier) = T.carrier",
			"∀a:A. a ∈ R.carrier ⇒ p(k(a)) = g(ideal_quotient_projection(R, J, a))",
		},
		Conclusion: "flat_module(R, «xOverBase») ∧ " +
			"ring_kernel(T.zero, X.carrier, p) = ideal_span(X, image(k, J)) ⇔ " +
			"∃i:(D → I). " +
			"    algebra_deformation(R, " +
			"        ideal_quotient_ring(R, J), " +
			"        ideal_quotient_projection(R, J), " +
			"        T, " +
			"        g, " +
			"        M, " +
			"        ι, " +
			"        mk_square_zero(X, k, i, p))",
		Abbrev: Abbrev{
			{Name: "tOverQuotient", Text: "scalar_restriction(g, regular_module(T))"},
			{Name: "jOverQuotient", Text: "ideal_quotient_module(R, J, restrict_module(regular_module(R), J))"},
			{Name: "xOverBase", Text: "scalar_restriction(k, regular_module(X))"},
		},
	},
		"⇒: build μ : (X/JX) ⊗_{R₀} J → X as the multiplication X ⊗_R J → X, x ⊗ j ↦ k(j)·x "+
			"(TensorUniversal over R), after the inverse of TensorSquareZeroBaseChange; "+
			"SquareZeroFlatForward makes it injective with image J·X, and J·X — the R-span of the "+
			"products k(j)·x — is ideal_span(k(J)) since that set of generators is closed under "+
			"multiples from X; X/JX ≅ T through p, so T ⊗_{R₀} J ≅ (X/JX) ⊗_{R₀} J, and i is μ after "+
			"that isomorphism and h⁻¹. The clauses of SquareZeroExtension hold because μ is linear "+
			"over X through p and J·J = 0, and k(j) = μ(1 ⊗ j) = i(ι(j)) (AlgebraDeformationDef). ⇐: "+
			"the kernel is J·X (DeformationKernelGenerated, ι(J) spanning M because the pure tensors "+
			"span, TensorSpan); μ is i after h after the isomorphism, so it is injective; X/JX ≅ T "+
			"is flat over R₀ (FlatIsomorphic); and SquareZeroFlatCriterion gives X flat over R"),
})}

// DeformationObstruction — in a universe for the three rings, T has a
// deformation over R exactly when the obstruction ∂¹(ξ) vanishes in
// D^2(T/R₀, M).
var DeformationObstruction = deformationObstructionThm{family.Add(registry.ProofEntry{
	Name: "DeformationObstruction",
	Key:  "prop_40723180d72d500e",
	Reading: "A deformation exists at some type exactly when one exists at set(prod(U, " +
		"D)), the type of the realizations, and the existence is stated there. The " +
		"obstruction lies in D^2 of T over R₀, not over R. With M = J ⊗_{R₀} T, ι(j) = j ⊗ " +
		"1 and T flat over R₀ it is the obstruction to a flat algebra over R lifting T.",
	Deps: []registry.EntryLike{
		AlgebraDeformationObstructionDef,
		ThickeningClassDef,
		DeformationIffPullbackClass,
		RightMapIsPullback,
		ThickeningIsExtension,
		PushoutIsExtension,
		CohomologyCoefficientRestriction,
		transitivity.CotangentCohomologyTransitivity,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_classification.SquareZeroRealizationDef,
		module_homomorphism.ExactAtDef,
		group_homomorphism.GroupKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
		},
		Conclusion: "(∀E:square_zero_ops(A, C, I, D). " +
			"    «deformation»(E) ⇒ " +
			"    algebra_deformation_obstruction⟨U:U⟩(R, R₀, f, T, g, M, ι) = " +
			"    «deformationTReduced»(2).zero) ∧ " +
			"(algebra_deformation_obstruction⟨U:U⟩(R, R₀, f, T, g, M, ι) = «deformationTReduced»(2).zero ⇒ " +
			"    ∃E:square_zero_ops(A, C, set(prod(U, D)), D). «deformation»(E))",
	},
		"a deformation is an extension whose pullback along g has class ξ "+
			"(DeformationIffPullbackClass), the pullback's class is the right map's image of the "+
			"extension's (RightMapIsPullback), and every class of D^1(T/R, M) is the class of its "+
			"realization (ExtensionRealizeClass, SquareZeroRealizationDef). So a deformation exists "+
			"exactly when ξ is in the right map's image, which is the kernel of the connecting map by "+
			"exactness at D^1(R₀/R, M) (CotangentCohomologyTransitivity, ExactAtDef, GroupKernelDef); "+
			"ξ is in D^1(R₀/R, M) (ExtensionClassWellDefined at the pushed thickening, "+
			"PushoutIsExtension, ThickeningIsExtension, CohomologyCoefficientRestriction), and its "+
			"connecting image is the obstruction (AlgebraDeformationObstructionDef, "+
			"ThickeningClassDef). For ⇐ the deformation is the realization of the class found"),
})}

// DeformationsTorsor — in a universe for the three rings, the classes of
// the deformations of T over R are a torsor under D^1(T/R₀, M): the
// realization of the class of a deformation plus i*(η) is a deformation,
// and the classes of two deformations differ by exactly one η.
var DeformationsTorsor = deformationsTorsorThm{family.Add(registry.ProofEntry{
	Name: "DeformationsTorsor",
	Key:  "prop_4040996153875c50",
	Reading: "Two deformations are isomorphic as extensions exactly when their " +
		"classes agree (ExtensionIsoIffSameClass), so the isomorphism classes of " +
		"deformations are a torsor under D^1(T/R₀, M), empty exactly when the obstruction " +
		"does not vanish (DeformationObstruction). The realization of ζ has class ζ " +
		"(ExtensionRealizeClass). Freeness needs f onto, through RestrictionMapInjective.",
	Deps: []registry.EntryLike{
		TowerExtensionTorsor,
		DeformationIffPullbackClass,
		RightMapIsPullback,
		PushoutIsExtension,
		ThickeningIsExtension,
		ThickeningClassDef,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_classification.ExtensionClassWellDefined,
		cotangent_complex.CotangentCohomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
		},
		Conclusion: "(∀E:square_zero_ops(A, C, I, D). ∀η:set(U → D). " +
			"    «deformation»(E) ∧ η ∈ «deformationTReduced»(1).carrier ⇒ " +
			"    «deformation»(square_zero_realization(R, " +
			"            T, " +
			"            λa:A. g(f(a)), " +
			"            M, " +
			"            «deformationTR»(1).add(«classOfT»(E), «deformationLeft»(η))))) ∧ " +
			"(∀E:square_zero_ops(A, C, I, D). ∀E':square_zero_ops(A, C, F, D). " +
			"    «deformation»(E) ∧ «deformation»(E') ⇒ " +
			"    ∃η:set(U → D). " +
			"        η ∈ «deformationTReduced»(1).carrier ∧ " +
			"        «classOfT»(E') = «deformationTR»(1).add(«classOfT»(E), «deformationLeft»(η)) ∧ " +
			"        (∀η':set(U → D). " +
			"            η' ∈ «deformationTReduced»(1).carrier ∧ " +
			"            «classOfT»(E') = «deformationTR»(1).add(«classOfT»(E), «deformationLeft»(η')) ⇒ " +
			"            η' = η))",
	},
		"the classes of the deformations are the classes of D^1(T/R, M) the right map sends to ξ "+
			"(DeformationIffPullbackClass, RightMapIsPullback, ExtensionRealizeClass), the classes "+
			"compatible with the pushed thickening, whose class is ξ (ThickeningClassDef); "+
			"TowerExtensionTorsor at that pushout (PushoutIsExtension, ThickeningIsExtension) is the torsor, "+
			"its action the one written here. The realization of the class of E plus i*(η) is an extension "+
			"with that class (ExtensionRealizeClass, CotangentCohomologyModuleOn), so a deformation"),
})}

// DeformationAutomorphisms — the automorphisms of a square-zero extension
// E of T by M over R — over R, the identity on M and over T — are the
// maps e ↦ e + i(d(p(e))) for the derivations d of T over R₀ into M, d
// determined on T's carrier, composition the sum of derivations.
var DeformationAutomorphisms = deformationAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "DeformationAutomorphisms",
	Key:  "prop_3b9ab15e8bb0b172",
	Reading: "For a deformation this is Aut(E) ≅ Der_{R₀}(T, M), the derivations D^0(T/R₀, M) " +
		"computes. The deformation condition is not read: every extension of T by M over R has " +
		"these automorphisms. f onto makes a derivation over R one over R₀, every member of R₀ " +
		"being some f(a); the square-zero clause makes the cross term i(d(p(e)))i(d(p(e'))) vanish.",
	Deps: []registry.EntryLike{
		square_zero_extension.SquareZeroExtension,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.DerivationShearAutomorphism,
		partial_derivative.DerivationOn,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.LiftDifferenceDerivation,
		square_zero_extension.InclusionAction,
		square_zero_extension.InclusionSquareZero,
		square_zero_extension.InclusionInjective,
		square_zero_extension.InclusionAdd,
		comm_ring.SubAddNegOn,
		comm_ring.LeftDistribOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"∀E:square_zero_ops(A, C, I, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
			"«extensionOfT»(E)",
		},
		Conclusion: "(∀d:(C → D). " +
			"    derivation_on(R₀, T, g, M, d) ⇒ " +
			"    square_zero_isomorphism(R, " +
			"        M, " +
			"        E, " +
			"        E, " +
			"        λe:I. E.ring.add(e, E.inclusion(d(E.projection(e)))))) ∧ " +
			"(∀φ:(I → I). " +
			"    square_zero_isomorphism(R, M, E, E, φ) ⇒ " +
			"    ∃d:(C → D). " +
			"        derivation_on(R₀, T, g, M, d) ∧ " +
			"        (∀e:I. e ∈ E.ring.carrier ⇒ φ(e) = E.ring.add(e, E.inclusion(d(E.projection(e)))))) ∧ " +
			"(∀d d':(C → D). " +
			"    derivation_on(R₀, T, g, M, d) ∧ " +
			"    derivation_on(R₀, T, g, M, d') ∧ " +
			"    (∀e:I. " +
			"        e ∈ E.ring.carrier ⇒ " +
			"        E.ring.add(e, E.inclusion(d(E.projection(e)))) = " +
			"        E.ring.add(e, E.inclusion(d'(E.projection(e))))) ⇒ " +
			"    ∀t:C. t ∈ T.carrier ⇒ d(t) = d'(t)) ∧ " +
			"(∀d d':(C → D). " +
			"    derivation_on(R₀, T, g, M, d) ∧ derivation_on(R₀, T, g, M, d') ⇒ " +
			"    ∀e:I. " +
			"        e ∈ E.ring.carrier ⇒ " +
			"        E.ring.add(E.ring.add(e, E.inclusion(d'(E.projection(e)))), " +
			"            E.inclusion(d(E.projection(E.ring.add(e, E.inclusion(d'(E.projection(e)))))))) = " +
			"        E.ring.add(e, E.inclusion(M.add(d(E.projection(e)), d'(E.projection(e))))))",
		Abbrev: Abbrev{
			{Name: "extensionOfT", Text: "square_zero_extension(R, T, λa:A. g(f(a)), M)"},
		},
	},
		"for a derivation d over R₀, e ↦ e + i(d(p(e))) keeps sums, and products by the Leibniz rule, "+
			"InclusionAction and InclusionSquareZero, as the shear does in DerivationShearAutomorphism; d "+
			"vanishes on g(f(a)) and on T.zero, so it fixes the structure map and the inclusion, and the "+
			"map of −d is its inverse (RingIsomorphismDef, SquareZeroIsomorphismDef). Conversely φ and the "+
			"identity are two lifts of the projection to E over the structure map (SquareZeroLiftDef), so "+
			"φ(e) − e = i(D(e)) for a derivation D of E's ring, LiftDifferenceDerivation at P = E.ring, h "+
			"= E.structure, ε = E.projection, s₁ = id, s₂ = φ; D kills i(M), which φ fixes, so D(e) "+
			"depends on p(e) only, which defines d on T, p being onto, a derivation over R vanishing on "+
			"g(f(a)), hence over R₀ as f is onto (DerivationOn). Uniqueness and the composite are "+
			"injectivity and additivity of i (InclusionInjective; InclusionAdd, MapAdd at the projection)"),
})}
