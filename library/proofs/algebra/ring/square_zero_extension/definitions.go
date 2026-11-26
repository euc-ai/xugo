// definitions.go — the chapter's definitional layer: the record a
// square-zero extension is held in and the structure on it, the
// isomorphisms and the lifts between extensions, and the constructions
// over an algebra P with a ring map ε onto S — the split extension
// P ⋉_ε N, the extension the graph of a conormal map defines in it, and
// the conormal map a lift reads off an extension. The graph and the
// shear are module_extension's, the same pair-level maps a module
// extension is built from.

package square_zero_extension

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ringHom says h is a ring homomorphism from the ring record r on its
// carrier to the ring record s on its carrier.
func ringHom(r, s, h string) string {
	return "ring_homomorphism(" + r + ", " + s + ", " + h + ")"
}

// ---------------------------------------------------------------------------
// The record and the structure
// ---------------------------------------------------------------------------

// SquareZeroOpsData — the record `square_zero_ops(A, B, C, D)`:
// `mk_square_zero(X, k, i, p)` packs the ring X of an extension on the
// type C, its structure map k from the base ring's type A, the inclusion
// i of the module's vectors D and the projection p onto the type B of
// the ring extended. Under a binder E of the type the parts read
// `E.ring`, `E.structure`, `E.inclusion`, `E.projection`.
var SquareZeroOpsData = family.DefineData(registry.DataEntry{
	Name:   "SquareZeroOps",
	Type:   "square_zero_ops",
	Params: []string{"A", "B", "C", "D"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_square_zero", Args: []string{"ring_ops(C)", "A → C", "D → C", "C → B"}},
	},
	Fields: []registry.DataField{
		{Name: "SquareZeroRingDef", Const: "square_zero_ring", Field: "ring"},
		{Name: "SquareZeroStructureDef", Const: "square_zero_structure", Field: "structure"},
		{Name: "SquareZeroInclusionDef", Const: "square_zero_inclusion", Field: "inclusion"},
		{Name: "SquareZeroProjectionDef", Const: "square_zero_projection", Field: "projection"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "SquareZeroOpsInduction",
		Recursion:      "SquareZeroOpsRecursion",
		Injective:      "MkSquareZeroInjective",
		Extensionality: "SquareZeroOpsEq",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		pairs.PairEq,
		pairs.Fst,
		pairs.Snd,
	},
})

// SquareZeroExtension — `square_zero_extension(R, S, f, N, E)`: E is a
// square-zero extension of the algebra S over R, through f, by the
// module N over S — the ring of E an algebra over R through its
// structure map, the projection an algebra map onto S, the inclusion an
// additive injection of N onto the kernel of the projection, the image
// of square zero, and E acting on it through the projection as S acts on
// N.
var SquareZeroExtension = squareZeroExtensionThm{family.DefineStructure(registry.DefEntry{
	Name:  "SquareZeroExtension",
	Key:   "prop_db84f1239c69614e",
	Const: "square_zero_extension",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"square_zero_ops(A, B, C, D) → " +
		"bool",
	Subject: "E",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀E:square_zero_ops(A, B, C, D). square_zero_extension(R, S, f, N, E) ⇔ " +
			ringHom(
				"R",
				"E.ring",
				"E.structure") + " ∧ " + ringHom(
			"E.ring",
			"S",
			"E.projection") + " ∧ image(E.projection, E.ring.carrier) = S.carrier ∧ (∀a:A. a ∈ R.carrier ⇒ E.projection(E.structure(a)) = f(a)) ∧ module_on(S, N) ∧ (∀n m:D. n ∈ N.carrier ∧ m ∈ N.carrier ⇒ E.inclusion(N.add(n, m)) = E.ring.add(E.inclusion(n), E.inclusion(m))) ∧ injective_on(N.carrier, E.inclusion) ∧ image(E.inclusion, N.carrier) = ring_kernel(S.zero, E.ring.carrier, E.projection) ∧ (∀n m:D. n ∈ N.carrier ∧ m ∈ N.carrier ⇒ E.ring.mul(E.inclusion(n), E.inclusion(m)) = E.ring.zero) ∧ (∀e:C. ∀n:D. e ∈ E.ring.carrier ∧ n ∈ N.carrier ⇒ E.ring.mul(e, E.inclusion(n)) = E.inclusion(N.smul(E.projection(e), n)))",
	},
	Reading: "The ring facts are conjoined, as derivation_on conjoins its own: a fact of the " +
		"structure carries R and the ring of E as commutative rings, S as one through the projection, " +
		"and N as a module over S. f need not be stated a ring map: it is the projection after the " +
		"structure map on R's carrier. The square-zero clause follows from the last one, i(n) * i(m) = " +
		"i(p(i(n)) • m) = i(S.zero • m) = i(N.zero), and is kept because it is what the name says. The " +
		"kernel of the projection is thus N with the module structure E/I = S.carrier gives it. The " +
		"host type C is free; two extensions on different types are compared by square_zero_isomorphism.",
})}

// SquareZeroIsomorphismDef — `square_zero_isomorphism(R, N, E, E', φ)`:
// φ is an isomorphism of the extensions E and E' — a ring isomorphism of
// their rings that commutes with the structure maps on R's carrier, with
// the inclusions on N's carrier and with the projections.
var SquareZeroIsomorphismDef = squareZeroIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroIsomorphismDef",
	Key:   "prop_2d17ff780738abff",
	Const: "square_zero_isomorphism",
	Type: "ring_ops(A) → " +
		"module_ops(B, D) → " +
		"square_zero_ops(A, B, C, D) → " +
		"square_zero_ops(A, B, I, D) → " +
		"(C → I) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D). " +
			"∀φ:(C → I). " +
			"    square_zero_isomorphism(R, N, E, E', φ) ⇔ " +
			"    ring_isomorphism(E.ring, E'.ring, φ) ∧ " +
			"    (∀a:A. a ∈ R.carrier ⇒ φ(E.structure(a)) = E'.structure(a)) ∧ " +
			"    (∀n:D. n ∈ N.carrier ⇒ φ(E.inclusion(n)) = E'.inclusion(n)) ∧ " +
			"    (∀e:C. e ∈ E.ring.carrier ⇒ E'.projection(φ(e)) = E.projection(e))",
	},
	Reading: "The rings may sit on different types C and I. φ is over R, the identity on N and " +
		"over S; it asks nothing of S itself, whose part in an extension is the projection's target.",
})}

// SquareZeroLiftDef — `square_zero_lift(R, P, h, ε, E, s)`: s is a lift
// of the ring map ε from the algebra P over R, through h, to the
// extension E — an algebra map over R from P to the ring of E whose
// projection is ε.
var SquareZeroLiftDef = squareZeroLiftDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroLiftDef",
	Key:   "prop_ce0eccb45d650968",
	Const: "square_zero_lift",
	Type: "ring_ops(A) → " +
		"ring_ops(U) → " +
		"(A → U) → " +
		"(U → B) → " +
		"square_zero_ops(A, B, C, D) → " +
		"(U → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀P:ring_ops(U). ∀h:(A → U). ∀ε:(U → B). ∀E:square_zero_ops(A, B, C, D). ∀s:(U → C). square_zero_lift(R, P, h, ε, E, s) ⇔ " +
			ringHom(
				"P",
				"E.ring",
				"s") + " ∧ (∀a:A. a ∈ R.carrier ⇒ s(h(a)) = E.structure(a)) ∧ (∀u:U. u ∈ P.carrier ⇒ E.projection(s(u)) = ε(u))",
	},
	Reading: "s is read on P's carrier only. Two lifts differ by a map into the " +
		"kernel of the projection, the image of N; on a polynomial algebra a lift exists " +
		"once the projection is onto, a preimage chosen for the image of each variable.",
})}

// ---------------------------------------------------------------------------
// The constructions over P
// ---------------------------------------------------------------------------

// SplitSquareZeroDef — `split_square_zero(P, ε, N)`: the split
// square-zero extension P ⋉_ε N — the pairs (u, n) of P's carrier and
// N's, added componentwise and multiplied by (u, n)(v, m) = (uv,
// ε(u) • m + ε(v) • n), with one (1, 0).
var SplitSquareZeroDef = splitSquareZeroDefThm{family.Define(registry.DefEntry{
	Name:  "SplitSquareZeroDef",
	Key:   "prop_36710e1d3fd236e2",
	Const: "split_square_zero",
	Type:  "ring_ops(U) → (U → B) → module_ops(B, D) → ring_ops(prod(U, D))",
	Equations: []string{
		"∀P:ring_ops(U). ∀ε:(U → B). ∀N:module_ops(B, D). " +
			"    split_square_zero(P, ε, N) = " +
			"    mk_ring(λz:prod(U, D). λw:prod(U, D).(P.add(fst(z), fst(w)), N.add(snd(z), snd(w))), " +
			"        (P.zero, N.zero), " +
			"        λz:prod(U, D).(P.neg(fst(z)), N.neg(snd(z))), " +
			"        λz:prod(U, D). " +
			"            λw:prod(U, D).(P.mul(fst(z), fst(w)), " +
			"                N.add(N.smul(ε(fst(z)), snd(w)), N.smul(ε(fst(w)), snd(z)))), " +
			"        (P.one, N.zero), " +
			"        λz:prod(U, D). λw:prod(U, D).(P.sub(fst(z), fst(w)), N.add(snd(z), N.neg(snd(w)))), " +
			"        set_cross(P.carrier, N.carrier))",
	},
	Reading: "N sits in it as the pairs (0, n), an ideal of square zero on which a pair acts " +
		"through ε of its first component: (u, n)(0, m) = (0, ε(u) • m). It is a commutative ring when P " +
		"is one, ε a ring map and N a module over S; u ↦ (u, 0) is a ring map, and so is (u, n) ↦ ε(u). " +
		"The operations are written through fst and snd, so they reduce at a pair by β and the pair laws.",
})}

// SquareZeroGraphDef — `square_zero_graph(P, h, S, ε, N, γ)`: the
// extension E_γ = (P ⋉_ε N)/J_γ defined by the conormal map γ — the ring
// of cosets of the graph of −γ over the kernel of ε, with structure map
// a ↦ [(h(a), 0)], inclusion n ↦ [(0, n)] and projection [(u, n)] ↦ ε(u).
var SquareZeroGraphDef = squareZeroGraphDefThm{family.Define(registry.DefEntry{
	Name:  "SquareZeroGraphDef",
	Key:   "prop_e0c38e62b6cc8263",
	Const: "square_zero_graph",
	Type: "ring_ops(U) → " +
		"(A → U) → " +
		"ring_ops(B) → " +
		"(U → B) → " +
		"module_ops(B, D) → " +
		"(U → D) → " +
		"square_zero_ops(A, B, set(prod(U, D)), D)",
	Equations: []string{
		"∀P:ring_ops(U). ∀h:(A → U). ∀S:ring_ops(B). ∀ε:(U → B). ∀N:module_ops(B, D). ∀γ:(U → D). " +
			"    square_zero_graph(P, h, S, ε, N, γ) = " +
			"    mk_square_zero(ideal_quotient_ring(split_square_zero(P, ε, N), " +
			"            twisted_graph(N, ring_kernel(S.zero, P.carrier, ε), γ)), " +
			"        λa:A. " +
			"            ideal_quotient_projection(split_square_zero(P, ε, N), " +
			"                twisted_graph(N, ring_kernel(S.zero, P.carrier, ε), γ), " +
			"                (h(a), N.zero)), " +
			"        λn:D. " +
			"            ideal_quotient_projection(split_square_zero(P, ε, N), " +
			"                twisted_graph(N, ring_kernel(S.zero, P.carrier, ε), γ), " +
			"                (P.zero, n)), " +
			"        induced_map(λz:prod(U, D). ε(fst(z))))",
	},
	Reading: "The projection reads a coset at its chosen member; the members of one " +
		"coset differ by a pair of the graph, whose first component lies in the kernel of " +
		"ε, so every member gives the same value. The extension lives on set(prod(U, D)) " +
		"whatever the conormal map; it is a square-zero extension of S by N when ε is onto.",
})}

// ExtractConormalDef — `extract_conormal(P, S, ε, N, E, s, x)`: the
// conormal map a lift s of ε to the extension E reads — at x in the
// kernel of ε the preimage of s(x) under the inclusion, N.zero off the
// kernel.
var ExtractConormalDef = extractConormalDefThm{family.Define(registry.DefEntry{
	Name:  "ExtractConormalDef",
	Key:   "prop_13d8eb3006dbe97b",
	Const: "extract_conormal",
	Type: "ring_ops(U) → " +
		"ring_ops(B) → " +
		"(U → B) → " +
		"module_ops(B, D) → " +
		"square_zero_ops(A, B, C, D) → " +
		"(U → C) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀P:ring_ops(U). " +
			"∀S:ring_ops(B). " +
			"∀ε:(U → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀s:(U → C). " +
			"∀x:U. " +
			"    extract_conormal(P, S, ε, N, E, s, x) = " +
			"    COND(x ∈ ring_kernel(S.zero, P.carrier, ε), inverse_on(N.carrier, E.inclusion, s(x)), N.zero)",
	},
	Reading: "A lift carries the kernel of ε into the kernel of the projection, the image of " +
		"N, so a preimage exists in N's carrier; the inclusion is injective there, so it is the one " +
		"preimage and γ_s(x) is i⁻¹(s(x)). Off the kernel the value is N.zero, as a conormal map asks.",
})}
