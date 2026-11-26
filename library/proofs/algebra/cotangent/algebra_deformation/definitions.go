// definitions.go — the chapter's definitional layer: the kernel of a
// square-zero thickening R → R₀ as a module over R₀; the pullback of a
// square-zero extension along an algebra map and its pushout along a
// linear map of modules, each a square_zero_ops record; the class ξ of
// the thickening pushed into a module; and, over a tower R → R₀ → T with
// a module M over T and a map ι from the kernel into M, the deformations
// of T over R and the obstruction ∂¹(ξ) to their existence.

package algebra_deformation

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The kernel of a thickening
// ---------------------------------------------------------------------------

// ThickeningKernelDef — `thickening_kernel(R, S, f)`: the kernel J of the
// ring map f from R to S, a module over S — R's sum on it, and a member b
// of S acting by multiplication with the preimage of b that inverse_on
// chooses.
var ThickeningKernelDef = thickeningKernelDefThm{family.Define(registry.DefEntry{
	Name:  "ThickeningKernelDef",
	Key:   "prop_22ca72feb8c8e40e",
	Const: "thickening_kernel",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    thickening_kernel(R, S, f) = " +
			"    restrict_module(scalar_restriction(inverse_on(R.carrier, f), regular_module(R)), " +
			"        ring_kernel(S.zero, R.carrier, f))",
	},
	Reading: "It is a module over S when f is onto and J has square zero " +
		"(ThickeningIsExtension): two preimages of b differ by a member of J, which " +
		"kills J, so the action is the one every preimage gives. Off the image of f " +
		"the chosen preimage is arbitrary; onto, no member of S's carrier is off it.",
})}

// ---------------------------------------------------------------------------
// Pullback and pushout
// ---------------------------------------------------------------------------

// SquareZeroPullbackDef — `square_zero_pullback(S, f, g, E)`: the
// pullback g*E of the extension E of T along the ring map g from S to T —
// the pairs (s, e) of S's carrier and E's ring with g(s) = p(e), under
// the componentwise operations, with structure map a ↦ (f(a), k(a)),
// inclusion n ↦ (0, i(n)) and the first projection.
var SquareZeroPullbackDef = squareZeroPullbackDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroPullbackDef",
	Key:   "prop_266b182b271f0aa2",
	Const: "square_zero_pullback",
	Type: "ring_ops(B) → " +
		"(A → B) → " +
		"(B → C) → " +
		"square_zero_ops(A, C, I, D) → " +
		"square_zero_ops(A, B, prod(B, I), D)",
	Equations: []string{
		"∀S:ring_ops(B). ∀f:(A → B). ∀g:(B → C). ∀E:square_zero_ops(A, C, I, D). " +
			"    square_zero_pullback(S, f, g, E) = " +
			"    mk_square_zero(mk_ring( " +
			"            λz:prod(B, I). λw:prod(B, I).(S.add(fst(z), fst(w)), E.ring.add(snd(z), snd(w))), " +
			"            (S.zero, E.ring.zero), " +
			"            λz:prod(B, I).(S.neg(fst(z)), E.ring.neg(snd(z))), " +
			"            λz:prod(B, I). λw:prod(B, I).(S.mul(fst(z), fst(w)), E.ring.mul(snd(z), snd(w))), " +
			"            (S.one, E.ring.one), " +
			"            λz:prod(B, I). λw:prod(B, I).(S.sub(fst(z), fst(w)), E.ring.sub(snd(z), snd(w))), " +
			"            {z:prod(B, I) | " +
			"                fst(z) ∈ S.carrier ∧ " +
			"                snd(z) ∈ E.ring.carrier ∧ " +
			"                g(fst(z)) = E.projection(snd(z))}), " +
			"        λa:A.(f(a), E.structure(a)), " +
			"        λn:D.(S.zero, E.inclusion(n)), " +
			"        λz:prod(B, I). fst(z))",
	},
	Reading: "f is S's structure map over R, read only by the structure map of the pullback; " +
		"R itself is not an argument. The pairs (S.zero, i(n)) are the kernel of the first " +
		"projection, so N is the kernel again, S acting on it through g (PullbackIsExtension).",
})}

// SquareZeroPushoutDef — `square_zero_pushout(N, N', ι, E)`: the pushout
// ι_*E of the extension E of S by N along the map ι from N to N' — the
// ring of cosets of E.ring ⋉ N' modulo the pairs (i(n), −ι(n)), with
// structure map a ↦ [(k(a), 0)], inclusion m ↦ [(0, m)] and projection
// [(e, m)] ↦ p(e).
var SquareZeroPushoutDef = squareZeroPushoutDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroPushoutDef",
	Key:   "prop_e5a55c3377d85167",
	Const: "square_zero_pushout",
	Type: "module_ops(B, F) → " +
		"module_ops(B, D) → " +
		"(F → D) → " +
		"square_zero_ops(A, B, I, F) → " +
		"square_zero_ops(A, B, set(prod(I, D)), D)",
	Equations: []string{
		"∀N:module_ops(B, F). ∀N':module_ops(B, D). ∀ι:(F → D). ∀E:square_zero_ops(A, B, I, F). " +
			"    square_zero_pushout(N, N', ι, E) = " +
			"    mk_square_zero(ideal_quotient_ring(split_square_zero(E.ring, E.projection, N'), " +
			"            image(λn:F.(E.inclusion(n), N'.neg(ι(n))), N.carrier)), " +
			"        λa:A. " +
			"            ideal_quotient_projection(split_square_zero(E.ring, E.projection, N'), " +
			"                image(λn:F.(E.inclusion(n), N'.neg(ι(n))), N.carrier), " +
			"                (E.structure(a), N'.zero)), " +
			"        λm:D. " +
			"            ideal_quotient_projection(split_square_zero(E.ring, E.projection, N'), " +
			"                image(λn:F.(E.inclusion(n), N'.neg(ι(n))), N.carrier), " +
			"                (E.ring.zero, m)), " +
			"        induced_map(λz:prod(I, D). E.projection(fst(z))))",
	},
	Reading: "Of N only the carrier is read. N' is a module over E.ring through " +
		"the projection, as in P ⋉_ε N; the relations are an ideal when ι is linear over " +
		"S, i(n) acting on N' by p(i(n)) = S.zero. In the quotient [(i(n), 0)] = [(0, " +
		"ι(n))], which is how the kernel of E is carried along ι (PushoutIsExtension).",
})}

// ---------------------------------------------------------------------------
// The class of the thickening
// ---------------------------------------------------------------------------

// ThickeningClassDef — `thickening_class(R, S, f, N, ι)`: the class ξ in
// D^1(S/R, N) of the thickening R → S, R itself as an extension of S by
// its kernel J over R, pushed along the map ι from J into the module N
// over S.
var ThickeningClassDef = thickeningClassDefThm{family.Define(registry.DefEntry{
	Name:  "ThickeningClassDef",
	Key:   "prop_55753670879b11d9",
	Const: "thickening_class",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, D) → (A → D) → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀ι:(A → D). " +
			"    thickening_class(R, S, f, N, ι) = " +
			"    square_zero_class(R, " +
			"        S, " +
			"        f, " +
			"        N, " +
			"        square_zero_pushout(thickening_kernel(R, S, f), " +
			"            N, " +
			"            ι, " +
			"            mk_square_zero(R, λa:A. a, λj:A. j, f)))",
	},
	Reading: "The thickening is the record of R with the identity as structure map, the " +
		"inclusion of J and f as projection, an extension when f is onto with square-zero " +
		"kernel (ThickeningIsExtension). Before the push its class in D^1(S/R, J) is zero " +
		"only when J is: a section σ over R has σ(f(a)) = a, so f is injective. The letter U " +
		"is fixed by the universe hypotheses of the statements, as square_zero_class's is.",
	Deps: []registry.EntryLike{ThickeningKernelDef, SquareZeroPushoutDef},
})}

// ---------------------------------------------------------------------------
// Deformations and their obstruction
// ---------------------------------------------------------------------------

// AlgebraDeformationDef — `algebra_deformation(R, R₀, f, T, g, M, ι, E)`:
// E is a deformation of the algebra T over R₀ to R — a square-zero
// extension of T by M over R whose structure map on the kernel J of f is
// the inclusion after ι.
var AlgebraDeformationDef = algebraDeformationDefThm{family.Define(registry.DefEntry{
	Name:  "AlgebraDeformationDef",
	Key:   "prop_cf65fdc3362e4204",
	Const: "algebra_deformation",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"(A → D) → " +
		"square_zero_ops(A, C, I, D) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"∀E:square_zero_ops(A, C, I, D). " +
			"    algebra_deformation(R, R₀, f, T, g, M, ι, E) ⇔ " +
			"    square_zero_extension(R, T, λa:A. g(f(a)), M, E) ∧ " +
			"    (∀j:A. j ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ E.structure(j) = E.inclusion(ι(j)))",
	},
	Reading: "The condition on J is the class condition f*[E] = ξ read concretely: the pullback of " +
		"E along g is the thickening pushed along ι exactly when it holds (DeformationIffPullbackClass). " +
		"With M = J ⊗_{R₀} T and ι(j) = j ⊗ 1, and T flat over R₀, a deformation is a flat algebra over " +
		"R lifting T; for any other M and ι it is an extension of T compatible with ι. The class is not " +
		"the definition because a class carries the host letter U, which this predicate's type does not.",
})}

// AlgebraDeformationObstructionDef —
// `algebra_deformation_obstruction(R, R₀, f, T, g, M, ι)`: the obstruction
// ∂¹(ξ) in D^2(T/R₀, M) to a deformation of T over R, the connecting map
// of the cohomology sequence of R → R₀ → T at the thickening class, M
// read over R₀ through g.
var AlgebraDeformationObstructionDef = algebraDeformationObstructionDefThm{family.Define(registry.DefEntry{
	Name:  "AlgebraDeformationObstructionDef",
	Key:   "prop_bd5c14d9afca13c",
	Const: "algebra_deformation_obstruction",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"(A → D) → " +
		"set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"    algebra_deformation_obstruction(R, R₀, f, T, g, M, ι) = " +
			"    co_transitivity_connecting(R, " +
			"        R₀, " +
			"        f, " +
			"        T, " +
			"        g, " +
			"        M, " +
			"        1, " +
			"        thickening_class(R, R₀, f, scalar_restriction(g, M), ι))",
	},
	Reading: "ξ is computed with M read over R₀ and the connecting map reads D^1(R₀/R, " +
		"M) with M over T; the two have the same classes (CohomologyCoefficientRestriction). " +
		"It vanishes exactly when a deformation exists (DeformationObstruction).",
	Deps: []registry.EntryLike{ThickeningClassDef},
})}
