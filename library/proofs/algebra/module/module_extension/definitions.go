// definitions.go — the chapter's definitional layer: the record a module
// extension is held in and the structure on it, the isomorphisms of
// extensions and the lifts into one, and the constructions over a module
// F with a linear map ε onto M — the graph of a map on the kernel of ε
// in the product F ⊕ N, the shear of the product by a map into N, the
// extension the graph defines, and the map on the kernel a lift reads
// off an extension.

package module_extension

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The record and the structure
// ---------------------------------------------------------------------------

// ModuleExtensionOpsData — the record `module_extension_ops(A, B, C,
// D)`: `mk_module_extension(X, i, p)` packs the module X of an extension
// on the type C over the scalars A, the inclusion i of the kernel's
// vectors D and the projection p onto the quotient's vectors B. Under a
// binder E of the type the parts read `E.module`, `E.inclusion`,
// `E.projection`.
var ModuleExtensionOpsData = family.DefineData(registry.DataEntry{
	Name:   "ModuleExtensionOps",
	Type:   "module_extension_ops",
	Params: []string{"A", "B", "C", "D"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_module_extension", Args: []string{"module_ops(A, C)", "D → C", "C → B"}},
	},
	Fields: []registry.DataField{
		{Name: "moduleExtensionModuleDef", Const: "module_extension_module", Field: "module"},
		{Name: "moduleExtensionInclusionDef", Const: "module_extension_inclusion", Field: "inclusion"},
		{Name: "moduleExtensionProjectionDef", Const: "module_extension_projection", Field: "projection"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "ModuleExtensionOpsInduction",
		Recursion:      "ModuleExtensionOpsRecursion",
		Injective:      "MkModuleExtensionInjective",
		Extensionality: "ModuleExtensionOpsEq",
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

// ModuleExtension — `module_extension(R, M, N, E)`: E is an extension of
// the module M by the module N over R — the sequence N → E.module → M of
// its inclusion and projection is short exact.
var ModuleExtension = moduleExtensionThm{family.DefineStructure(registry.DefEntry{
	Name:  "ModuleExtension",
	Key:   "prop_3a43c5b8888ac417",
	Const: "module_extension",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, D) → " +
		"module_extension_ops(A, B, C, D) → " +
		"bool",
	Subject: "E",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀E:module_extension_ops(A, B, C, D). " +
			"    module_extension(R, M, N, E) ⇔ " +
			"    short_exact_modules(R, N, E.module, M, E.inclusion, E.projection)",
	},
	Reading: "The short exact sequence carries the three modules: both maps are homomorphisms, " +
		"and module_homomorphism conjoins its endpoints. The module of E sits on a type C of its " +
		"own; two extensions on different types are compared by module_extension_isomorphism. No " +
		"splitting is asked: the split extension is the product, whose class is zero.",
})}

// ModuleExtensionIsomorphismDef — `module_extension_isomorphism(R, N, E,
// E', φ)`: φ is an isomorphism of the extensions E and E' — an
// isomorphism of their modules that commutes with the inclusions on N's
// carrier and with the projections.
var ModuleExtensionIsomorphismDef = moduleExtensionIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleExtensionIsomorphismDef",
	Key:   "prop_2765ee67286227fe",
	Const: "module_extension_isomorphism",
	Type: "ring_ops(A) → " +
		"module_ops(A, D) → " +
		"module_extension_ops(A, B, C, D) → " +
		"module_extension_ops(A, B, I, D) → " +
		"(C → I) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:module_ops(A, D). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀E':module_extension_ops(A, B, I, D). " +
			"∀φ:(C → I). " +
			"    module_extension_isomorphism(R, N, E, E', φ) ⇔ " +
			"    module_isomorphism(R, E.module, E'.module, φ) ∧ " +
			"    (∀n:D. n ∈ N.carrier ⇒ φ(E.inclusion(n)) = E'.inclusion(n)) ∧ " +
			"    (∀e:C. e ∈ E.module.carrier ⇒ E'.projection(φ(e)) = E.projection(e))",
	},
	Reading: "The modules may sit on different types C and I. φ is the identity on N and " +
		"over M; it asks nothing of M itself, whose part in an extension is the projection's target.",
})}

// ModuleExtensionLiftDef — `module_extension_lift(R, F, ε, E, s)`: s is a
// lift of the linear map ε from F to the extension E — a homomorphism
// from F to the module of E whose projection is ε.
var ModuleExtensionLiftDef = moduleExtensionLiftDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleExtensionLiftDef",
	Key:   "prop_9ddf82fa9eaece7a",
	Const: "module_extension_lift",
	Type: "ring_ops(A) → " +
		"module_ops(A, U) → " +
		"(U → B) → " +
		"module_extension_ops(A, B, C, D) → " +
		"(U → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀s:(U → C). " +
			"    module_extension_lift(R, F, ε, E, s) ⇔ " +
			"    module_homomorphism(R, F, E.module, s) ∧ (∀u:U. u ∈ F.carrier ⇒ E.projection(s(u)) = ε(u))",
	},
	Reading: "s is read on F's carrier only. Two lifts differ by a map into " +
		"the kernel of the projection, the image of N; for F free and the projection " +
		"onto a lift exists, a preimage chosen for the image of each generator.",
})}

// ---------------------------------------------------------------------------
// The constructions over F
// ---------------------------------------------------------------------------

// TwistedGraphDef — `twisted_graph(N, I, γ)`: the graph of −γ over I,
// {(x, −γ(x)) | x ∈ I}.
var TwistedGraphDef = twistedGraphDefThm{family.Define(registry.DefEntry{
	Name:  "TwistedGraphDef",
	Key:   "prop_b1b33e8d2b8de9b7",
	Const: "twisted_graph",
	Type:  "module_ops(B, D) → set(U) → (U → D) → set(prod(U, D))",
	Equations: []string{
		"∀N:module_ops(B, D). ∀I:set(U). ∀γ:(U → D). " +
			"    twisted_graph(N, I, γ) = image(λx:U. (x, N.neg(γ(x))), I)",
	},
	Reading: "Only N's negation is read, so one graph serves both chapters that build an " +
		"extension from it. At I the kernel of a linear map ε : F → M and γ linear on I it is a " +
		"submodule of F ⊕ N; at I the kernel of a ring map ε : P → S and γ a conormal map it is " +
		"an ideal of P ⋉_ε N (algebra/ring/square_zero_extension). Modulo the graph the pair " +
		"(x, 0) is the pair (0, γ(x)): the quotient reads γ back as the map a lift carries I by.",
})}

// DerivationShearDef — `derivation_shear(N, d, z)`: the shear of the pair
// z by the map d, (u, n) ↦ (u, n − d(u)).
var DerivationShearDef = derivationShearDefThm{family.Define(registry.DefEntry{
	Name:  "DerivationShearDef",
	Key:   "prop_936b9b42002bf887",
	Const: "derivation_shear",
	Type:  "module_ops(B, D) → (U → D) → prod(U, D) → prod(U, D)",
	Equations: []string{
		"∀N:module_ops(B, D). ∀d:(U → D). ∀z:prod(U, D). " +
			"    derivation_shear(N, d, z) = (fst(z), N.add(snd(z), N.neg(d(fst(z)))))",
	},
	Reading: "Only N's sum and negation are read. For d linear from F to N it is a " +
		"module automorphism of F ⊕ N; for d a derivation of P into N along ε a ring " +
		"automorphism of P ⋉_ε N (algebra/ring/square_zero_extension). Either way it is the " +
		"identity on the first component and on the pairs (0, n), its inverse is the shear " +
		"by −d, and it carries the graph of −γ over the kernel to the graph of −(γ + d).",
})}

// ModuleExtensionGraphDef — `module_extension_graph(F, M, ε, N, φ)`: the
// extension E_φ = (F ⊕ N)/J_φ defined by the map φ on the kernel of ε —
// the module of cosets of the graph of −φ over the kernel, with
// inclusion n ↦ [(0, n)] and projection [(u, n)] ↦ ε(u).
var ModuleExtensionGraphDef = moduleExtensionGraphDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleExtensionGraphDef",
	Key:   "prop_9b43b6994331cea4",
	Const: "module_extension_graph",
	Type: "module_ops(A, U) → " +
		"module_ops(A, B) → " +
		"(U → B) → " +
		"module_ops(A, D) → " +
		"(U → D) → " +
		"module_extension_ops(A, B, set(prod(U, D)), D)",
	Equations: []string{
		"∀F:module_ops(A, U). ∀M:module_ops(A, B). ∀ε:(U → B). ∀N:module_ops(A, D). ∀φ:(U → D). " +
			"    module_extension_graph(F, M, ε, N, φ) = " +
			"    mk_module_extension(quotient_module(product_module(F, N), " +
			"            twisted_graph(N, group_kernel(M.zero, F.carrier, ε), φ)), " +
			"        λn:D. " +
			"            left_coset(product_module(F, N).add, " +
			"                (F.zero, n), " +
			"                twisted_graph(N, group_kernel(M.zero, F.carrier, ε), φ)), " +
			"        induced_map(λz:prod(U, D). ε(fst(z))))",
	},
	Reading: "The projection reads a coset at its chosen member; the members of one " +
		"coset differ by a pair of the graph, whose first component lies in the kernel of ε, " +
		"so every member gives the same value. The extension lives on set(prod(U, D)) whatever " +
		"φ is; it is an extension of M by N when ε is onto and φ is linear on the kernel.",
})}

// ExtractSyzygyMapDef — `extract_syzygy_map(F, M, ε, N, E, s, x)`: the map
// on the kernel of ε a lift s of ε to the extension E reads — at x in
// the kernel the preimage of s(x) under the inclusion, N.zero off it.
var ExtractSyzygyMapDef = extractSyzygyMapDefThm{family.Define(registry.DefEntry{
	Name:  "ExtractSyzygyMapDef",
	Key:   "prop_e68d4ca98b2aece9",
	Const: "extract_syzygy_map",
	Type: "module_ops(A, U) → " +
		"module_ops(A, B) → " +
		"(U → B) → " +
		"module_ops(A, D) → " +
		"module_extension_ops(A, B, C, D) → " +
		"(U → C) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀F:module_ops(A, U). " +
			"∀M:module_ops(A, B). " +
			"∀ε:(U → B). " +
			"∀N:module_ops(A, D). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀s:(U → C). " +
			"∀x:U. " +
			"    extract_syzygy_map(F, M, ε, N, E, s, x) = " +
			"    COND(x ∈ group_kernel(M.zero, F.carrier, ε), " +
			"        inverse_on(N.carrier, E.inclusion, s(x)), " +
			"        N.zero)",
	},
	Reading: "A lift carries the kernel of ε into the kernel of the projection, " +
		"the image of N, so a preimage exists in N's carrier; the inclusion is " +
		"injective there, so it is the one preimage and φ_s(x) is i⁻¹(s(x)). Off the " +
		"kernel the value is N.zero, as a member of hom_set on the kernel asks.",
})}
