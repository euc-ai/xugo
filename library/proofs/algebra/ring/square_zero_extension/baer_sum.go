// baer_sum.go — the Baer sum of two square-zero extensions E and E' of
// an algebra S over R by one module N: the fiber product of their rings,
// the pairs (e, e') over one member of S, modulo the pairs (i(n),
// −i'(n)). It is again an extension of S by N, with structure map
// a ↦ [(k(a), k'(a))] and inclusion n ↦ [(i(n), 0)] = [(0, i'(n))]. Up
// to isomorphism the sum respects isomorphisms, is commutative and
// associative, has the split extension S ⋉ N as its unit and E with its
// inclusion negated as the inverse of E, and commutes with localizing at
// a lift. Every isomorphism here is a named map on cosets.

package square_zero_extension

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the Baer sum
// ---------------------------------------------------------------------------

// baerPairOperation spells the binary operation op of the fiber product
// of E and E': E's op on the first components, E”s on the second.
func baerPairOperation(op string) string {
	return "λz:prod(C, I). λw:prod(C, I). (E.ring." + op + "(fst(z), fst(w)), E'.ring." + op + "(snd(z), snd(w)))"
}

// baerFiber is the fiber product of the extensions X and Y.
func baerFiber(X, Y string) string { return "square_zero_fiber_product(" + X + ", " + Y + ")" }

// baerAntidiagonal spells the pairs (i(m), −i'(m)) for m in N's carrier,
// the ideal of the fiber product of X and Y that the Baer sum divides by;
// vec is the type of N's members. baerClass is the coset of the pair z
// modulo it, the class of z in the Baer sum.
func baerAntidiagonal(N, X, Y, vec string) string {
	return "image(λm:" + vec + ". (" + X + ".inclusion(m), " + Y + ".ring.neg(" + Y + ".inclusion(m))), " + N + ".carrier)"
}

func baerClass(N, X, Y, vec, z string) string {
	return "ideal_quotient_projection(" + baerFiber(
		X, Y) + ", " + baerAntidiagonal(N, X, Y, vec) + ", " + z + ")"
}

// baerInduced applies the map that the function lam induces on cosets to
// the coset x; with x empty it is the map itself.
func baerInduced(lam, x string) string {
	if x == "" {
		return "induced_map(" + lam + ")"
	}
	return "induced_map(" + lam + ", " + x + ")"
}

// ---------------------------------------------------------------------------
// The fiber product and the Baer sum
// ---------------------------------------------------------------------------

// SquareZeroFiberProductDef — `square_zero_fiber_product(E, E')`: the
// ring E ×_S E' of the pairs (e, e') of the rings of two extensions with
// one projection, p(e) = p'(e'), under the componentwise operations.
var SquareZeroFiberProductDef = squareZeroFiberProductDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroFiberProductDef",
	Key:   "prop_11c5753b096aea54",
	Const: "square_zero_fiber_product",
	Type:  "square_zero_ops(A, B, C, D) → square_zero_ops(A, B, I, D) → ring_ops(prod(C, I))",
	Equations: []string{
		"∀E:square_zero_ops(A, B, C, D). ∀E':square_zero_ops(A, B, I, D). square_zero_fiber_product(E, E') = mk_ring(" +
			baerPairOperation(
				"add") + ", (E.ring.zero, E'.ring.zero), λz:prod(C, I). (E.ring.neg(fst(z)), E'.ring.neg(snd(z))), " +
			baerPairOperation("mul") + ", (E.ring.one, E'.ring.one), " + baerPairOperation(
			"sub") + ", {z:prod(C, I) | fst(z) ∈ E.ring.carrier ∧ snd(z) ∈ E'.ring.carrier ∧ E.projection(fst(z)) = E'.projection(snd(z))})",
	},
	Reading: "Only the two rings and the two projections are read. It is a " +
		"commutative ring when E and E' are extensions of one ring S (BaerSumIsExtension): " +
		"the ring of the pullback of E' along the projection of E. The operations are " +
		"written through fst and snd, so they reduce at a pair by β and the pair laws.",
	Deps: []registry.EntryLike{SquareZeroOpsData.Ext, SquareZeroRingDef, SquareZeroProjectionDef},
})}

// SquareZeroBaerSumDef — `square_zero_baer_sum(N, E, E')`: the Baer sum
// of the extensions E and E' by N — their fiber product modulo the pairs
// (i(n), −i'(n)), with structure map a ↦ [(k(a), k'(a))], inclusion
// n ↦ [(i(n), 0)] and projection [(e, e')] ↦ p(e).
var SquareZeroBaerSumDef = squareZeroBaerSumDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroBaerSumDef",
	Key:   "prop_785c8f25368acf66",
	Const: "square_zero_baer_sum",
	Type: "module_ops(B, D) → " +
		"square_zero_ops(A, B, C, D) → " +
		"square_zero_ops(A, B, I, D) → " +
		"square_zero_ops(A, B, set(prod(C, I)), D)",
	Equations: []string{
		"∀N:module_ops(B, D). ∀E:square_zero_ops(A, B, C, D). ∀E':square_zero_ops(A, B, I, D). square_zero_baer_sum(N, E, E') = mk_square_zero(ideal_quotient_ring(" + baerFiber(
			"E",
			"E'") + ", " + baerAntidiagonal(
			"N",
			"E",
			"E'",
			"D") + "), λa:A. " + baerClass(
			"N",
			"E",
			"E'",
			"D",
			"(E.structure(a), E'.structure(a))") + ", λn:D. " + baerClass(
			"N", "E", "E'", "D", "(E.inclusion(n), E'.ring.zero)") + ", " +
			baerInduced("λz:prod(C, I). E.projection(fst(z))", "") + ")",
	},
	Reading: "The projection reads a coset at its chosen member: two members differ by " +
		"a pair (i(n), −i'(n)), on which E's projection is S.zero, so on two extensions " +
		"every member gives the same value, which is p'(e') as well. Of N only the carrier " +
		"is read. The class of (0, i'(n)) is the inclusion of n too (BaerSumIsExtension), so " +
		"the sum treats its two summands alike. It lives on set(prod(C, I)) whatever the two " +
		"are; its class is the sum of the two classes (algebra_deformation's BaerSumClass).",
	Deps: []registry.EntryLike{
		SquareZeroFiberProductDef,
		SquareZeroOpsData.Ext,
		SquareZeroRingDef,
		SquareZeroStructureDef,
		SquareZeroInclusionDef,
		SquareZeroProjectionDef,
	},
})}

// ---------------------------------------------------------------------------
// The Baer sum is an extension
// ---------------------------------------------------------------------------

// BaerSumIsExtension — for two extensions E and E' of S by N over R, the
// fiber product is a commutative ring in which the pairs (i(n), −i'(n))
// are an ideal, the Baer sum is a square-zero extension of S by N over R,
// its projection reads the class of (e, e') as p(e), and the class of
// (0, i'(n)) is the inclusion of n.
var BaerSumIsExtension = baerSumIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "BaerSumIsExtension",
	Key:  "prop_147ba92f30a0d581",
	Reading: "The rings may sit on different types. p(e) = p'(e') is what makes the antidiagonal " +
		"absorb the product: (e, e')(i(n), −i'(n)) = (i(p(e) • n), −i'(p'(e') • n)) is the antidiagonal " +
		"pair at p(e) • n. The last conjunct is the identity [(0, i'(n))] = [(i(n), 0)], their " +
		"difference the antidiagonal pair at −n: the kernel of the sum is N read through either " +
		"summand. N zero makes the antidiagonal the zero pair and the sum the fiber product, a copy of S.",
	Deps: []registry.EntryLike{
		SquareZeroBaerSumDef,
		SquareZeroFiberProductDef,
		SquareZeroExtension,
		SquareZeroOpsData.Ext,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.IdealQuotientRingDef,
		quotient_ring.IdealQuotientProjectionDef,
		quotient_ring.CosetEqIff,
		quotient_ring.QuotientMulCoset,
		equivalence.InducedMapDef,
		ring_ideal.RingIdealDef,
		comm_ring.CommRingOn,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.RingKernelDef,
		ProjectionHomomorphism,
		ProjectionOnto,
		ProjectionOverBase,
		InclusionAdd,
		InclusionAction,
		InclusionInjective,
		InclusionZero,
		InclusionImage,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D).",
		Hypotheses: []string{
			"«baerExtension»(E)",
			"«baerExtension»(E')",
		},
		Conclusion: "comm_ring_on(square_zero_fiber_product(E, E')) ∧ " +
			"ring_ideal(square_zero_fiber_product(E, E'), " +
			"    image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier)) ∧ " +
			"«baerExtension»(square_zero_baer_sum(N, E, E')) ∧ " +
			"(∀z:prod(C, I). " +
			"    z ∈ square_zero_fiber_product(E, E').carrier ⇒ " +
			"    square_zero_baer_sum(N, E, E').projection(ideal_quotient_projection( " +
			"            square_zero_fiber_product(E, E'), " +
			"            image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"            z)) = " +
			"    E.projection(fst(z))) ∧ " +
			"(∀n:D. " +
			"    n ∈ N.carrier ⇒ " +
			"    ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"        image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"        (E.ring.zero, E'.inclusion(n))) = " +
			"    square_zero_baer_sum(N, E, E').inclusion(n))",
		Abbrev: Abbrev{
			{Name: "baerExtension", Text: "square_zero_extension(R, S, f, N)"},
		},
	},
		"unfold SquareZeroFiberProductDef: the operations are componentwise at pairs (Fst, Snd, PairEq) "+
			"and the carrier is closed under them, both projections being ring maps to S "+
			"(ProjectionHomomorphism, MapAdd, MapMul, MapOne), so it is a commutative ring (CommRingOn). The "+
			"antidiagonal is an ideal (RingIdealDef): its pairs lie over S.zero, it holds the zero pair, is "+
			"closed under sums, i and i' being additive (InclusionAdd), and (e, e')(i(n), −i'(n)) = (i(p(e) "+
			"• n), −i'(p'(e') • n)) by InclusionAction with p(e) = p'(e'). The cosets are a commutative ring "+
			"and the coset map a ring map onto them (IdealQuotientProjection, IdealQuotientRingDef). The "+
			"projection is well defined, members of a coset differing by an antidiagonal pair (CosetEqIff, "+
			"InducedMapDef), a ring map onto S, and f after the structure map (ProjectionOnto, "+
			"ProjectionOverBase). The inclusion is additive and injective, (i(n), 0) = (i(m), −i'(m)) "+
			"forcing i'(m) = 0, m = N.zero and n = N.zero (InclusionInjective, InclusionZero); its image is "+
			"the kernel, [(i(n), i'(m))] = [(i(n + m), 0)] (InclusionImage, RingKernelDef); [(e, e')][(i(n), "+
			"0)] = [(i(p(e) • n), 0)] gives the action and the square zero (QuotientMulCoset). The last "+
			"conjunct: (0, i'(n)) − (i(n), 0) is the antidiagonal pair at −n (CosetEqIff)"),
})}

// BaerSumIsomorphism — isomorphic extensions have isomorphic Baer sums:
// for isomorphisms φ from E to X and φ' from E' to X', the class of
// (e, e') going to the class of (φ(e), φ'(e')) is an isomorphism of the
// Baer sums.
var BaerSumIsomorphism = baerSumIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "BaerSumIsomorphism",
	Key:  "prop_1204cbcf2dfc6b72",
	Reading: "The map is read on cosets: a member (e + i(n), e' − i'(n)) goes to " +
		"(φ(e) + i_X(n), φ'(e') − i_X'(n)), in the coset of (φ(e), φ'(e')) because " +
		"both isomorphisms are the identity on N. It is how the Baer sum passes to " +
		"isomorphism classes, and how a gluing of each summand gives one of the sum.",
	Deps: []registry.EntryLike{
		BaerSumIsExtension,
		SquareZeroBaerSumDef,
		SquareZeroFiberProductDef,
		SquareZeroIsomorphismDef,
		SquareZeroExtension,
		quotient_ring.QuotientFirstIso,
		quotient_ring.CosetEqIff,
		quotient_ring.IdealQuotientProjection,
		equivalence.InducedMapDef,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.RingKernelDef,
		functions.InjectiveOnDef,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D). " +
			"∀X:square_zero_ops(A, B, H, D). " +
			"∀X':square_zero_ops(A, B, G, D). " +
			"∀φ:(C → H). " +
			"∀φ':(I → G).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"square_zero_extension(R, S, f, N, E')",
			"square_zero_extension(R, S, f, N, X)",
			"square_zero_extension(R, S, f, N, X')",
			"square_zero_isomorphism(R, N, E, X, φ)",
			"square_zero_isomorphism(R, N, E', X', φ')",
		},
		Conclusion: "square_zero_isomorphism(R, " +
			"    N, " +
			"    square_zero_baer_sum(N, E, E'), " +
			"    square_zero_baer_sum(N, X, X'), " +
			"    induced_map(λw:prod(C, I). " +
			"            ideal_quotient_projection(square_zero_fiber_product(X, X'), " +
			"                image(λm:D. (X.inclusion(m), X'.ring.neg(X'.inclusion(m))), N.carrier), " +
			"                (φ(fst(w)), φ'(snd(w)))))) ∧ " +
			"(∀z:prod(C, I). " +
			"    z ∈ square_zero_fiber_product(E, E').carrier ⇒ " +
			"    induced_map(λw:prod(C, I). " +
			"            ideal_quotient_projection(square_zero_fiber_product(X, X'), " +
			"                image(λm:D. (X.inclusion(m), X'.ring.neg(X'.inclusion(m))), N.carrier), " +
			"                (φ(fst(w)), φ'(snd(w)))), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"            image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"            z)) = " +
			"    ideal_quotient_projection(square_zero_fiber_product(X, X'), " +
			"        image(λm:D. (X.inclusion(m), X'.ring.neg(X'.inclusion(m))), N.carrier), " +
			"        (φ(fst(z)), φ'(snd(z)))))",
	},
		"(e, e') ↦ (φ(e), φ'(e')) carries the fiber product of E and E' onto that of X and X', the "+
			"projections commuting with φ and φ' (SquareZeroIsomorphismDef, Fst, Snd, PairEq), and is "+
			"a ring map; followed by the coset map (IdealQuotientProjection, BaerSumIsExtension) it is "+
			"a ring map onto the Baer sum of X and X' whose kernel is the antidiagonal: [(φ(e), "+
			"φ'(e'))] = 0 makes it (i_X(n), −i_X'(n)), which is (φ(i(n)), φ'(−i'(n))), so (e, e') = "+
			"(i(n), −i'(n)) by injectivity (RingKernelDef, CosetEqIff, InjectiveOnDef). "+
			"QuotientFirstIso gives the ring isomorphism and its value on cosets (InducedMapDef). Over "+
			"R, the identity on N and over S: [(k(a), k'(a))] ↦ [(k_X(a), k_X'(a))], [(i(n), 0)] ↦ "+
			"[(i_X(n), 0)], and p_X(φ(e)) = p(e) (SquareZeroIsomorphismDef, RingIsomorphismDef)"),
})}

// ---------------------------------------------------------------------------
// The group laws up to isomorphism
// ---------------------------------------------------------------------------

// BaerSumSplitUnit — the split extension S ⋉ N is a unit: it is an
// extension of S by N, and the class of (e, (y, n)) going to e + i(n) is
// an isomorphism from the Baer sum of E and S ⋉ N onto E.
var BaerSumSplitUnit = baerSumSplitUnitThm{family.Add(registry.ProofEntry{
	Name: "BaerSumSplitUnit",
	Key:  "prop_9a4de518b5b3019",
	Reading: "S ⋉ N is P ⋉_ε N at P = S and ε the identity, with structure map a ↦ " +
		"(f(a), 0) and the first projection, as SplitExtensionClassZero writes it. The " +
		"map adds the split pair's second component into E: a coset member (e + i(m), (y, " +
		"n − m)) goes to e + i(n) again, so no representative is read. f is a ring map on " +
		"R's carrier because it is p ∘ k there, which is all the split extension asks.",
	Deps: []registry.EntryLike{
		BaerSumIsExtension,
		SquareZeroBaerSumDef,
		SplitSquareZeroRing,
		SplitSquareZeroDef,
		SquareZeroExtension,
		SquareZeroIsomorphismDef,
		quotient_ring.QuotientFirstIso,
		quotient_ring.CosetEqIff,
		equivalence.InducedMapDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.RingKernelDef,
		comm_ring.LeftDistribOn,
		comm_ring.RightDistribOn,
		StructureHomomorphism,
		ProjectionHomomorphism,
		ProjectionOverBase,
		InclusionAction,
		InclusionSquareZero,
		InclusionInjective,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
		},
		Conclusion: "square_zero_extension(R, S, f, N, «split»(S, f, N)) ∧ " +
			"square_zero_isomorphism(R, " +
			"    N, " +
			"    square_zero_baer_sum(N, E, «split»(S, f, N)), " +
			"    E, " +
			"    induced_map(λw:prod(C, prod(B, D)). E.ring.add(fst(w), E.inclusion(snd(snd(w)))))) ∧ " +
			"(∀e:C. ∀n:D. " +
			"    e ∈ E.ring.carrier ∧ n ∈ N.carrier ⇒ " +
			"    induced_map(λw:prod(C, prod(B, D)). E.ring.add(fst(w), E.inclusion(snd(snd(w)))), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E, «split»(S, f, N)), " +
			"            image(λm:D. " +
			"                    (E.inclusion(m), «split»(S, f, N).ring.neg(«split»(S, f, N).inclusion(m))), " +
			"                N.carrier), " +
			"            (e, E.projection(e), n))) = " +
			"    E.ring.add(e, E.inclusion(n)))",
	},
		"S ⋉ N is an extension of S by N over R: a commutative ring with (y, n) ↦ y a ring map onto S "+
			"and y ↦ (y, 0) a section (SplitSquareZeroRing at P = S, ε the identity), f = p ∘ k a ring map "+
			"on R's carrier (StructureHomomorphism, ProjectionHomomorphism, ProjectionOverBase), and the "+
			"clauses of SquareZeroExtension at the pairs (S.zero, n) (SplitSquareZeroDef). (e, (y, n)) ↦ e + "+
			"i(n) is a ring map from the fiber product onto E's ring: at a product the cross terms e i(n') + "+
			"e' i(n) are i(p(e) • n' + p(e') • n), the split product's second component, by InclusionAction "+
			"and InclusionSquareZero (LeftDistribOn, RightDistribOn), and (e, (p(e), 0)) ↦ e. Its kernel is "+
			"the antidiagonal: e + i(n) = 0 makes e = i(−n) and y = p(e) = S.zero, the antidiagonal pair at "+
			"−n (RingKernelDef, InclusionInjective). QuotientFirstIso gives the ring isomorphism and its "+
			"value on cosets (BaerSumIsExtension, CosetEqIff, InducedMapDef). Over R: [(k(a), (f(a), 0))] ↦ "+
			"k(a); on N: [(i(n), (0, 0))] ↦ i(n); over S: p(e + i(n)) = p(e) (SquareZeroIsomorphismDef)"),
})}

// BaerSumComm — the Baer sum is commutative: the class of (e, e') going
// to the class of (e', e) is an isomorphism from the Baer sum of E and E'
// onto that of E' and E.
var BaerSumComm = baerSumCommThm{family.Add(registry.ProofEntry{
	Name: "BaerSumComm",
	Key:  "prop_2f3086c3a9891014",
	Reading: "A coset member (e + i(n), e' − i'(n)) goes to (e' − i'(n), e + i(n)), the antidiagonal " +
		"pair of E' and E at −n away from (e', e), so the map is well defined. The two sums sit on " +
		"set(prod(C, I)) and set(prod(I, C)), so the isomorphism is a map between types, not an equation.",
	Deps: []registry.EntryLike{
		BaerSumIsExtension,
		SquareZeroBaerSumDef,
		SquareZeroFiberProductDef,
		SquareZeroIsomorphismDef,
		quotient_ring.QuotientFirstIso,
		quotient_ring.CosetEqIff,
		equivalence.InducedMapDef,
		ring_homomorphism.RingKernelDef,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"square_zero_extension(R, S, f, N, E')",
		},
		Conclusion: "square_zero_isomorphism(R, " +
			"    N, " +
			"    square_zero_baer_sum(N, E, E'), " +
			"    square_zero_baer_sum(N, E', E), " +
			"    induced_map(λw:prod(C, I). " +
			"            ideal_quotient_projection(square_zero_fiber_product(E', E), " +
			"                image(λm:D. (E'.inclusion(m), E.ring.neg(E.inclusion(m))), N.carrier), " +
			"                (snd(w), fst(w))))) ∧ " +
			"(∀z:prod(C, I). " +
			"    z ∈ square_zero_fiber_product(E, E').carrier ⇒ " +
			"    induced_map(λw:prod(C, I). " +
			"            ideal_quotient_projection(square_zero_fiber_product(E', E), " +
			"                image(λm:D. (E'.inclusion(m), E.ring.neg(E.inclusion(m))), N.carrier), " +
			"                (snd(w), fst(w))), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"            image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"            z)) = " +
			"    ideal_quotient_projection(square_zero_fiber_product(E', E), " +
			"        image(λm:D. (E'.inclusion(m), E.ring.neg(E.inclusion(m))), N.carrier), " +
			"        (snd(z), fst(z))))",
	},
		"the swap (e, e') ↦ (e', e) is a ring isomorphism of the fiber products "+
			"(SquareZeroFiberProductDef, Fst, Snd, PairEq); followed by the coset map it is a ring "+
			"map onto the Baer sum of E' and E (BaerSumIsExtension) whose kernel is the antidiagonal "+
			"of E and E', (e', e) = (i'(n), −i(n)) being (e, e') = (i(−n), −i'(−n)) (RingKernelDef, "+
			"CosetEqIff). QuotientFirstIso gives the isomorphism and its value on cosets "+
			"(InducedMapDef). Over R and over S at once; on N: [(i(n), 0)] ↦ [(0, i(n))], which is "+
			"[(i'(n), 0)] by the last conjunct of BaerSumIsExtension (SquareZeroIsomorphismDef)"),
})}

// BaerSumAssoc — the Baer sum is associative: the class of ([(e, e')],
// e”) going to the class of (e, [(e', e”)]) is an isomorphism from
// (E ⊕ E') ⊕ E” onto E ⊕ (E' ⊕ E”).
var BaerSumAssoc = baerSumAssocThm{family.Add(registry.ProofEntry{
	Name: "BaerSumAssoc",
	Key:  "prop_884f5745eed6a010",
	Reading: "Both sums are quotients of the triples (e, e', e'') over one member of S by " +
		"the triples (i(n), i'(m), i''(l)) with n + m + l = 0; the map reads that at nested " +
		"cosets, one representative of each level, and every choice gives one class. The two " +
		"iterated sums sit on set(prod(set(prod(C, I)), H)) and set(prod(C, set(prod(I, H)))).",
	Deps: []registry.EntryLike{
		BaerSumIsExtension,
		SquareZeroBaerSumDef,
		SquareZeroFiberProductDef,
		SquareZeroIsomorphismDef,
		SquareZeroExtension,
		quotient_ring.QuotientFirstIso,
		quotient_ring.CosetEqIff,
		quotient_ring.IdealQuotientProjection,
		equivalence.InducedMapDef,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.RingIsomorphismDef,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D). " +
			"∀E'':square_zero_ops(A, B, H, D).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"square_zero_extension(R, S, f, N, E')",
			"square_zero_extension(R, S, f, N, E'')",
		},
		Conclusion: "square_zero_isomorphism(R, " +
			"    N, " +
			"    square_zero_baer_sum(N, square_zero_baer_sum(N, E, E'), E''), " +
			"    square_zero_baer_sum(N, E, square_zero_baer_sum(N, E', E'')), " +
			"    induced_map(λw:prod(set(prod(C, I)), H). " +
			"            induced_map(λz:prod(C, I). " +
			"                    ideal_quotient_projection( " +
			"                        square_zero_fiber_product(E, square_zero_baer_sum(N, E', E'')), " +
			"                        image(λm:D. " +
			"                                (E.inclusion(m), " +
			"                                    square_zero_baer_sum(N, E', E'').ring.neg( " +
			"                                        square_zero_baer_sum(N, E', E'').inclusion(m))), " +
			"                            N.carrier), " +
			"                        (fst(z), " +
			"                            ideal_quotient_projection(square_zero_fiber_product(E', E''), " +
			"                                image(λm:D. (E'.inclusion(m), E''.ring.neg(E''.inclusion(m))), " +
			"                                    N.carrier), " +
			"                                (snd(z), snd(w))))), " +
			"                fst(w)))) ∧ " +
			"(∀e:C. ∀e':I. ∀e'':H. " +
			"    e ∈ E.ring.carrier ∧ " +
			"    e' ∈ E'.ring.carrier ∧ " +
			"    e'' ∈ E''.ring.carrier ∧ " +
			"    E.projection(e) = E'.projection(e') ∧ " +
			"    E'.projection(e') = E''.projection(e'') ⇒ " +
			"    induced_map(λw:prod(set(prod(C, I)), H). " +
			"            induced_map(λz:prod(C, I). " +
			"                    ideal_quotient_projection( " +
			"                        square_zero_fiber_product(E, square_zero_baer_sum(N, E', E'')), " +
			"                        image(λm:D. " +
			"                                (E.inclusion(m), " +
			"                                    square_zero_baer_sum(N, E', E'').ring.neg( " +
			"                                        square_zero_baer_sum(N, E', E'').inclusion(m))), " +
			"                            N.carrier), " +
			"                        (fst(z), " +
			"                            ideal_quotient_projection(square_zero_fiber_product(E', E''), " +
			"                                image(λm:D. (E'.inclusion(m), E''.ring.neg(E''.inclusion(m))), " +
			"                                    N.carrier), " +
			"                                (snd(z), snd(w))))), " +
			"                fst(w)), " +
			"        ideal_quotient_projection( " +
			"            square_zero_fiber_product(square_zero_baer_sum(N, E, E'), E''), " +
			"            image(λm:D. " +
			"                    (square_zero_baer_sum(N, E, E').inclusion(m), " +
			"                        E''.ring.neg(E''.inclusion(m))), " +
			"                N.carrier), " +
			"            (ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"                    image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"                    (e, e')), " +
			"                e''))) = " +
			"    ideal_quotient_projection(square_zero_fiber_product(E, square_zero_baer_sum(N, E', E'')), " +
			"        image(λm:D. " +
			"                (E.inclusion(m), " +
			"                    square_zero_baer_sum(N, E', E'').ring.neg( " +
			"                        square_zero_baer_sum(N, E', E'').inclusion(m))), " +
			"            N.carrier), " +
			"        (e, " +
			"            ideal_quotient_projection(square_zero_fiber_product(E', E''), " +
			"                image(λm:D. (E'.inclusion(m), E''.ring.neg(E''.inclusion(m))), N.carrier), " +
			"                (e', e'')))))",
	},
		"(x, e'') ↦ [(e, [(e', e'')])] for (e, e') in x is well defined: a member of the coset of (x, "+
			"e'') is (x + [(i(m), 0)], e'' − i''(m)), and a member of x + [(i(m), 0)] is (e + i(m + n), "+
			"e' − i'(n)); its image differs from [(e, [(e', e'')])] by (i(m + n), [(−i'(n), −i''(m))]), "+
			"and [(−i'(n), −i''(m))] = [(−i'(m + n), 0)], the two differing by the antidiagonal pair "+
			"(i'(m), −i''(m)) of E' and E'': an antidiagonal pair of E and E' ⊕ E'' at m + n "+
			"(BaerSumIsExtension, CosetEqIff). It is a ring map from the fiber product of E ⊕ E' and E'' "+
			"— the triples over one member of S, computed componentwise (SquareZeroFiberProductDef, "+
			"IdealQuotientProjection, Fst, Snd, PairEq) — onto E ⊕ (E' ⊕ E''), with kernel the "+
			"antidiagonal (RingKernelDef), so QuotientFirstIso gives the ring isomorphism and its value "+
			"on cosets (InducedMapDef). The structure maps, the inclusions [([(i(n), 0)], 0)] ↦ [(i(n), "+
			"[(0, 0)])] and the projections p(e) match (SquareZeroIsomorphismDef, SquareZeroBaerSumDef)"),
})}

// BaerSumInverse — E with its inclusion negated, n ↦ −i(n), is an
// extension of S by N, and the class of (e, e') going to
// (p(e), i⁻¹(e − e')) is an isomorphism from its Baer sum with E onto the
// split extension S ⋉ N.
var BaerSumInverse = baerSumInverseThm{family.Add(registry.ProofEntry{
	Name: "BaerSumInverse",
	Key:  "prop_11847011ebe4283a",
	Reading: "The antidiagonal of E and its negation is the pairs (i(n), i(n)), so the " +
		"difference e − e' of a pair over one member of S is constant on a coset; it lies in the " +
		"kernel of the projection, the image of N, and inverse_on reads its one preimage. The " +
		"inverse isomorphism sends (y, n) to [(e + i(n), e)] for any e over y. The negated extension " +
		"has the same ring, structure map and projection as E; its class is the negative of E's.",
	Deps: []registry.EntryLike{
		BaerSumIsExtension,
		BaerSumSplitUnit,
		SquareZeroBaerSumDef,
		SquareZeroFiberProductDef,
		SquareZeroExtension,
		SquareZeroIsomorphismDef,
		SplitSquareZeroRing,
		SplitSquareZeroDef,
		quotient_ring.QuotientFirstIso,
		quotient_ring.CosetEqIff,
		equivalence.InducedMapDef,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.AdditiveHomomorphism,
		comm_ring.SubAddNegOn,
		comm_ring.LeftDistribOn,
		InclusionAdd,
		InclusionInjective,
		InclusionImage,
		InclusionSquareZero,
		InclusionAction,
		InclusionInverse,
		InclusionInverseAdd,
		InclusionInverseMul,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
		},
		Conclusion: "square_zero_extension(R, S, f, N, «E⁻») ∧ " +
			"square_zero_isomorphism(R, " +
			"    N, " +
			"    square_zero_baer_sum(N, E, «E⁻»), " +
			"    «split»(S, f, N), " +
			"    induced_map( " +
			"        λw:prod(C, C). (E.projection(fst(w)), «coefficient»(E.ring.sub(fst(w), snd(w)))))) ∧ " +
			"(∀e e':C. " +
			"    e ∈ E.ring.carrier ∧ e' ∈ E.ring.carrier ∧ E.projection(e) = E.projection(e') ⇒ " +
			"    induced_map( " +
			"        λw:prod(C, C). (E.projection(fst(w)), «coefficient»(E.ring.sub(fst(w), snd(w)))), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E, «E⁻»), " +
			"            image(λm:D. (E.inclusion(m), «E⁻».ring.neg(«E⁻».inclusion(m))), N.carrier), " +
			"            (e, e'))) = " +
			"    (E.projection(e), «coefficient»(E.ring.sub(e, e'))))",
		Abbrev: Abbrev{
			{Name: "E⁻", Text: "mk_square_zero(E.ring, " +
				"    E.structure, " +
				"    λn:D. E.ring.neg(E.inclusion(n)), " +
				"    E.projection)"},
		},
	},
		"the negated inclusion is additive, injective and onto the kernel, of square zero, and e(−i(n)) "+
			"= −i(p(e) • n) (InclusionAdd, InclusionInjective, InclusionImage, InclusionSquareZero, "+
			"InclusionAction, AdditiveHomomorphism): the negation is an extension. For (e, e') over one "+
			"member of S, e − e' has projection S.zero, so it lies in the kernel and i⁻¹(e − e') is its "+
			"coefficient in N (InclusionInverse), and (e, e') ↦ (p(e), i⁻¹(e − e')) is a ring map from the "+
			"fiber product onto S ⋉ N (SplitSquareZeroRing, SplitSquareZeroDef): it keeps sums "+
			"(InclusionInverseAdd), and e₁e₂ − e₁'e₂' = e₁(e₂ − e₂') + (e₁ − e₁')e₂' (LeftDistribOn, "+
			"SubAddNegOn) has coefficient p(e₁) • n₂ + p(e₂) • n₁ (InclusionInverseAdd, "+
			"InclusionInverseMul), onto since (y, n) is the image of (e + i(n), e). Its kernel is the pairs "+
			"(i(n), i(n)), the antidiagonal (RingKernelDef, CosetEqIff); QuotientFirstIso gives the ring "+
			"isomorphism and its value on cosets (InducedMapDef). Over R: [(k(a), k(a))] ↦ (f(a), N.zero); "+
			"on N: [(i(n), 0)] ↦ (S.zero, n); over S: the first component (SquareZeroIsomorphismDef)"),
})}

// ---------------------------------------------------------------------------
// The Baer sum localized at a lift
// ---------------------------------------------------------------------------

// BaerSumLocalizes — for extensions E and E' of S by N over R with lifts
// t₀ and t₀' of one t, the Baer sum localized at the lift [(t₀, t₀')] is
// isomorphic to the Baer sum of the two localizations: the class of
// [(e, e')] over the k-th power of the lift goes to the class of
// (e/t₀ᵏ, e'/t₀'ᵏ).
var BaerSumLocalizes = baerSumLocalizesThm{family.Add(registry.ProofEntry{
	Name: "BaerSumLocalizes",
	Key:  "prop_1a7cce6a5d8f8d34",
	Reading: "[(t₀, t₀')] lies over t, so the sum localized there is an extension of S' by " +
		"N', and so is the Baer sum of the localizations. The map is written as the union, over " +
		"the representations (x, τᵏ) of a fraction class, x = [(e, e')], of the classes they " +
		"give, as SquareZeroLocalizationIndependent writes its map: two representations differ, " +
		"after a power of τ, by an antidiagonal pair (i(n), −i'(n)), which the localizations read " +
		"as the inclusion of the m with ρ(tʲ) • m = ν(n) and its negative. S' and N' are any " +
		"localizations; with S' a ring in which t is a unit and ρ, ν the identities this is the " +
		"reading biaffine_deformation's gluing of a Baer sum goes through. The representatives e " +
		"and e' are taken in the carriers: off them E's operations are unconstrained, so a pair " +
		"off the carrier can share a coset with a pair on it and give another fraction.",
	Deps: []registry.EntryLike{
		BaerSumIsExtension,
		SquareZeroBaerSumDef,
		SquareZeroFiberProductDef,
		SquareZeroLocalizationDef,
		SquareZeroLocalizationIsExtension,
		SquareZeroIsomorphismDef,
		SquareZeroExtension,
		ring_localization.LocalizationUniversal,
		ring_localization.ToFractionIsLocalization,
		ring_localization.FractionClassEq,
		ring_localization.FractionZeroIff,
		ring_localization.DenominatorUnit,
		ring_localization.IsLocalizationOnDef,
		ring_localization.IsModuleLocalizationOnDef,
		ring_localization.FractionMulClass,
		quotient_ring.CosetEqIff,
		quotient_ring.IdealQuotientProjection,
		comm_monoid.MapPow,
		comm_monoid.MonoidPowersDef,
		ring_homomorphism.RingIsomorphismDef,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D). " +
			"∀t:B. " +
			"∀t₀:C. " +
			"∀t_0':I. " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"square_zero_extension(R, S, f, N, E)",
			"square_zero_extension(R, S, f, N, E')",
			"t₀ ∈ E.ring.carrier",
			"E.projection(t₀) = t",
			"t_0' ∈ E'.ring.carrier",
			"E'.projection(t_0') = t",
			"«baseLocalization»",
			"«coefficientLocalization»",
		},
		Conclusion: "square_zero_isomorphism(R, " +
			"    N', " +
			"    square_zero_localization(N, " +
			"        S', " +
			"        ρ, " +
			"        N', " +
			"        ν, " +
			"        square_zero_baer_sum(N, E, E'), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"            image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"            (t₀, t_0'))), " +
			"    square_zero_baer_sum(N', " +
			"        square_zero_localization(N, S', ρ, N', ν, E, t₀), " +
			"        square_zero_localization(N, S', ρ, N', ν, E', t_0')), " +
			"    λX:set(prod(prod(C, I) → bool, prod(C, I) → bool)). " +
			"        ⋃{ " +
			"            ideal_quotient_projection(square_zero_fiber_product(square_zero_localization(N, S', ρ, N', ν, E, t₀), square_zero_localization(N, S', ρ, N', ν, E', t_0')), image(λm:G. (square_zero_localization(N, S', ρ, N', ν, E, t₀).inclusion(m), square_zero_localization(N, S', ρ, N', ν, E', t_0').ring.neg(square_zero_localization(N, S', ρ, N', ν, E', t_0').inclusion(m))), N'.carrier), (fraction_class(E.ring.mul, E.ring.carrier, monoid_powers(E.ring.mul, E.ring.one, t₀), e, monoid_pow(E.ring.mul, E.ring.one, t₀, k)), fraction_class(E'.ring.mul, E'.ring.carrier, monoid_powers(E'.ring.mul, E'.ring.one, t_0'), e', monoid_pow(E'.ring.mul, E'.ring.one, t_0', k)))):set( " +
			"                prod(prod(C, C) → bool, prod(I, I) → bool)) | " +
			"            e:C, " +
			"            e':I, " +
			"            k:num | " +
			"            e ∈ E.ring.carrier ∧ " +
			"            e' ∈ E'.ring.carrier ∧ " +
			"            (ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"                    image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"                    (e, e')), " +
			"                monoid_pow(square_zero_baer_sum(N, E, E').ring.mul, " +
			"                    square_zero_baer_sum(N, E, E').ring.one, " +
			"                    ideal_quotient_projection(square_zero_fiber_product(E, E'), " +
			"                        image(λm:D. (E.inclusion(m), E'.ring.neg(E'.inclusion(m))), N.carrier), " +
			"                        (t₀, t_0')), " +
			"                    k)) ∈ " +
			"            X})",
	},
		"τ = [(t₀, t₀')] lies in the sum over t (BaerSumIsExtension), so the localization of the sum "+
			"at τ is an extension of S' by N' (SquareZeroLocalizationIsExtension), and so is the Baer sum "+
			"of the localizations of E and E' (SquareZeroLocalizationIsExtension, BaerSumIsExtension). The "+
			"powers of τ are the classes [(t₀ᵏ, t₀'ᵏ)] (IdealQuotientProjection, MapPow, MonoidPowersDef). "+
			"[(e, e')] ↦ [(e/1, e'/1)] is a ring map from the sum carrying τ to a unit (DenominatorUnit), "+
			"so LocalizationUniversal at ToFractionIsLocalization gives a ring map from the localization "+
			"whose value at x/τᵏ is the class written, each representation giving it (FractionClassEq, "+
			"FractionMulClass, CosetEqIff, the last conjunct of SquareZeroLocalizationIsExtension for the "+
			"inclusions). Injective: a class sent to zero makes (e/t₀ᵏ, e'/t₀'ᵏ) an antidiagonal pair, so "+
			"after a power of τ, (e, e') is one (FractionZeroIff, IsLocalizationOnDef and the kernel "+
			"condition of IsModuleLocalizationOnDef, InjectiveOnDef). Onto: a pair over one member of S', "+
			"(e/t₀ʲ, e'/t₀'ʲ) at a common power, has tᵐ p(e) = tᵐ p'(e') for some m (IsLocalizationOnDef), "+
			"so it is the image of [(t₀ᵐ e, t₀'ᵐ e')]/τ^(m+j). Over R, on N' and over S' the maps read at "+
			"representatives (SquareZeroIsomorphismDef, RingIsomorphismDef)"),
})}
