// kaehler.go — the module of Kähler differentials of an algebra S over
// a ring R along a ring map f: the free module over S on the members of
// S's carrier, modulo the submodule its relations span — the generator
// of a sum minus the sum of the generators, the generator of a product
// minus the Leibniz combination, and the generator of every constant
// f(a). Its vectors are cosets of finitely supported functions on S's
// carrier, the universal derivation takes u to the coset of its
// generator, and every derivation into a module over S factors through
// it by one homomorphism. The differentials of the free algebra are the
// free module on its variables, through the partial derivatives, and a
// tower R → S → T has the first fundamental exact sequence.

package kaehler

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// The free module over S on S's carrier lives at B → B, S's operations
// read pointwise; these spell its record, a generator, a difference, a
// sum and a scaling.
const freeRecord = "free_module_record(S, S.carrier)"

func generator(u string) string { return "delta_at(S.zero, S.one, " + u + ")" }
func minus(x, y string) string {
	return "fun_add(S.add, " + x + ", fun_neg(S.neg, " + y + "))"
}
func plus(x, y string) string  { return "fun_add(S.add, " + x + ", " + y + ")" }
func scale(c, x string) string { return "fun_smul(S.mul, " + c + ", " + x + ")" }

// relations are the three kinds of relation element, as one set: the
// sums, the products and the constants.
var relations = "{r:(B → B) | ∃u v:B. u ∈ S.carrier ∧ v ∈ S.carrier ∧ r = " +
	minus(
		generator("S.add(u, v)"),
		plus(
			generator("u"), generator("v"))) + "} ∪ {r:(B → B) | ∃u v:B. u ∈ S.carrier ∧ v ∈ S.carrier ∧ r = " +
	minus(
		generator("S.mul(u, v)"),
		plus(
			scale("u", generator("v")),
			scale(
				"v", generator("u")))) + "} ∪ {r:(B → B) | ∃a:A. a ∈ R.carrier ∧ r = " + generator("f(a)") + "}"

// binders is the definitions' common ∀-prefix: the base ring, the
// algebra and its structure map.
const binders = "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). "
const kaehlerType = "ring_ops(A) → ring_ops(B) → (A → B) → "

// ---------------------------------------------------------------------------
// The module of differentials
// ---------------------------------------------------------------------------

// KaehlerRelationsDef — `kaehler_relations(R, S, f)`: the submodule of
// the free module over S on S's carrier spanned by δ_{u+v} − (δ_u + δ_v)
// and δ_{uv} − (u • δ_v + v • δ_u) for u, v in S's carrier, and by
// δ_{f(a)} for a in R's carrier.
var KaehlerRelationsDef = kaehlerRelationsDefThm{family.Define(registry.DefEntry{
	Name:  "KaehlerRelationsDef",
	Key:   "prop_520d11672393098b",
	Const: "kaehler_relations",
	Type:  kaehlerType + "set(B → B)",
	Equations: []string{
		binders + "kaehler_relations(R, S, f) = module_span(S, " + freeRecord + ", " + relations + ")",
	},
	Reading: "The span is the meet of the submodules holding the generators, and a submodule lies " +
		"in the free module, so a generator outside it — δ_{f(a)} with f(a) outside S's carrier — leaves " +
		"no submodule to meet and the span is the whole type. Every statement about the differentials " +
		"therefore asks f to be a ring map into S, which puts each generator in the free module.",
})}

// KaehlerModuleDef — `kaehler_module(R, S, f)`: Ω_{S/R}, the free module
// over S on S's carrier modulo the relations, a module record over S
// whose vectors are the cosets.
var KaehlerModuleDef = kaehlerModuleDefThm{family.Define(registry.DefEntry{
	Name:  "KaehlerModuleDef",
	Key:   "prop_7838229f0f67b0be",
	Const: "kaehler_module",
	Type:  kaehlerType + "module_ops(B, set(B → B))",
	Equations: []string{
		binders + "kaehler_module(R, S, f) = quotient_module(" + freeRecord + ", kaehler_relations(R, S, f))",
	},
	Reading: "The zero vector is the relations themselves, so Ω_{S/R} = 0 reads " +
		"`kaehler_module(R, S, f).carrier = {kaehler_module(R, S, f).zero}`. R enters only through " +
		"the image of its carrier under f: two structure maps with one image give one module.",
	Deps: []registry.EntryLike{KaehlerRelationsDef},
})}

// UniversalDerivationDef — `universal_derivation(R, S, f, u)`: the
// differential du, the coset of the generator at u.
var UniversalDerivationDef = universalDerivationDefThm{family.Define(registry.DefEntry{
	Name:  "UniversalDerivationDef",
	Key:   "prop_ab1cd4b8ca89e4d3",
	Const: "universal_derivation",
	Type:  kaehlerType + "B → set(B → B)",
	Equations: []string{
		binders + "∀u:B. universal_derivation(R, S, f, u) = left_coset(fun_add(S.add), " + generator(
			"u") + ", kaehler_relations(R, S, f))",
	},
	Reading: "At a u outside S's carrier the generator is not in the free module and its " +
		"coset is no vector of the module, so statements read du at members of the carrier. Over " +
		"the zero ring every generator is the zero function and du is the zero vector for every u.",
	Deps: []registry.EntryLike{KaehlerRelationsDef},
})}

// KaehlerRelationsSubmodule — the relations are a submodule of the free
// module over S on S's carrier.
var KaehlerRelationsSubmodule = kaehlerRelationsSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "KaehlerRelationsSubmodule",
	Key:  "prop_41b635b0727a7bbb",
	Deps: []registry.EntryLike{
		KaehlerRelationsDef,
		submodule.SpanSubmodule,
		free_module.FreeModuleOn,
		free_module.DeltaAtIn,
		ring_homomorphism.Target,
		ring_homomorphism.MapIn,
		comm_ring.AddIn,
		comm_ring.MulIn,
		module.SmulIn,
		group.MulIn,
		group.InvIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "submodule(S, free_module_record(S, S.carrier), kaehler_relations(R, S, f))",
	},
		"SpanSubmodule in the free module on S's carrier, a module over S since the ring "+
			"map's target conjunct makes S a commutative ring (Target, FreeModuleOn); each "+
			"relation element lies there: the generators at u + v, u * v, u and v are in it "+
			"(DeltaAtIn, AddIn, MulIn), it is closed under sums, negation and scaling, and "+
			"δ_{f(a)} is a generator since f carries R's carrier into S's (MapIn)"),
})}

// KaehlerModuleOn — the differentials of S over R form a module over S.
var KaehlerModuleOn = kaehlerModuleOnThm{family.Add(registry.ProofEntry{
	Name: "KaehlerModuleOn",
	Key:  "prop_6b2a4d71f8f5e28b",
	Deps: []registry.EntryLike{
		KaehlerModuleDef,
		KaehlerRelationsSubmodule,
		submodule.QuotientModuleOn,
		free_module.FreeModuleOn,
		ring_homomorphism.Target,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "module_on(S, kaehler_module(R, S, f))",
	},
		"QuotientModuleOn at the free module on S's carrier (FreeModuleOn) "+
			"and the relations submodule (KaehlerRelationsSubmodule)"),
})}

// UniversalDerivationIsDerivation — u ↦ du is a derivation of S over R
// into the differentials.
var UniversalDerivationIsDerivation = universalDerivationIsDerivationThm{family.Add(registry.ProofEntry{
	Name: "UniversalDerivationIsDerivation",
	Key:  "prop_f84d6d7e05e1a1e9",
	Deps: []registry.EntryLike{
		partial_derivative.DerivationOn,
		UniversalDerivationDef,
		KaehlerModuleDef,
		KaehlerRelationsDef,
		KaehlerModuleOn,
		KaehlerRelationsSubmodule,
		submodule.SubsetSpan,
		submodule.SubmoduleNormal,
		submodule.QuotientSmulCoset,
		quotient_group.LeftCosetMulOn,
		quotient_group.InLeftCosets,
		group.LeftCosetEqOn,
		group.LeftCosetOneOn,
		free_module.DeltaAtIn,
		set_basic.InUnion,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "derivation_on(R, S, f, kaehler_module(R, S, f), universal_derivation(R, S, f))",
	},
		"the conjuncts in order: the ring map is the hypothesis; the module is KaehlerModuleOn; du "+
			"is the coset of a generator of the free module (DeltaAtIn, InLeftCosets); the coset sum and "+
			"the quotient scaling compute on representatives (LeftCosetMulOn, QuotientSmulCoset), and "+
			"δ_{u+v} − (δ_u + δ_v) and δ_{uv} − (u • δ_v + v • δ_u) lie in the relations (SubsetSpan), "+
			"so the cosets agree (LeftCosetEqOn); δ_{f(a)} lies in the relations, so its coset is the "+
			"coset of the zero, the relations themselves, the zero vector (LeftCosetEqOn, LeftCosetOneOn)"),
})}

// KaehlerSpan — the differentials span the module: Ω_{S/R} is generated
// over S by the du, u in S's carrier.
var KaehlerSpan = kaehlerSpanThm{family.Add(registry.ProofEntry{
	Name: "KaehlerSpan",
	Key:  "prop_7fe926c0bd23498a",
	Deps: []registry.EntryLike{
		KaehlerModuleDef,
		UniversalDerivationDef,
		KaehlerModuleOn,
		KaehlerRelationsSubmodule,
		UniversalDerivationIsDerivation,
		free_module.FreeModuleExpand,
		free_module.FreeModuleOn,
		module_homomorphism.ProjectionHom,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		submodule.SpanSubmodule,
		submodule.SubsetSpan,
		submodule.SubmoduleModuleOn,
		module.ModuleSumIn,
		quotient_group.InLeftCosets,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "kaehler_module(R, S, f).carrier = " +
			"module_span(S, kaehler_module(R, S, f), image(universal_derivation(R, S, f), S.carrier))",
	},
		"the span lies in the carrier, a submodule holding every du (SpanSubmodule, "+
			"UniversalDerivationIsDerivation); a vector is the coset of some x in the free module, x = "+
			"Σ_{u ∈ supp x} x(u) • δ_u (FreeModuleExpand), and the projection onto the cosets is a "+
			"homomorphism (ProjectionHom), so the vector is Σ x(u) • du (HomSum, HomSmul), a finite sum of "+
			"scaled members of every submodule holding the differentials (SubmoduleModuleOn, ModuleSumIn)"),
})}

// KaehlerOntoVanishes — an algebra whose structure map is onto has no
// differentials: Ω_{S/R} = 0. At S = R and f the identity, Ω_{R/R} = 0.
var KaehlerOntoVanishes = kaehlerOntoVanishesThm{family.Add(registry.ProofEntry{
	Name: "KaehlerOntoVanishes",
	Key:  "prop_79d4aef83f726678",
	Deps: []registry.EntryLike{
		KaehlerSpan,
		UniversalDerivationIsDerivation,
		partial_derivative.DerivationOn,
		KaehlerModuleOn,
		submodule.ZeroSubmodule,
		submodule.SpanLeast,
		set_basic.InImage,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"image(f, R.carrier) = S.carrier",
		},
		Conclusion: "kaehler_module(R, S, f).carrier = {kaehler_module(R, S, f).zero}",
	},
		"every member of S's carrier is some f(a), so every du is d(f(a)), the zero vector "+
			"(UniversalDerivationIsDerivation's last conjunct); the span of the differentials then "+
			"lies in the zero submodule (ZeroSubmodule, SpanLeast), and it is the carrier (KaehlerSpan)"),
})}

// ---------------------------------------------------------------------------
// The universal property
// ---------------------------------------------------------------------------

// DerivationComposeHomomorphism — a derivation followed by a
// homomorphism of modules over S is a derivation.
var DerivationComposeHomomorphism = derivationComposeHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "DerivationComposeHomomorphism",
	Key:  "prop_ef31a6ac17b0917f",
	Deps: []registry.EntryLike{
		partial_derivative.DerivationOn,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomIn,
		module_homomorphism.HomAdd,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
		module_homomorphism.HomTarget,
	},
	Build: family.Card(partial_derivative.DerivationOn.Statement(Statement{
		Binders: "∀N':module_ops(B, E). ∀h:(C → E).",
		Hypotheses: []string{
			"module_homomorphism(S, N, N', h)",
		},
		Conclusion: "derivation_on(R, S, f, N', h ∘ D)",
	}),
		"the ring map is D's; N' is a module (HomTarget); h carries D's values into N' "+
			"(HomIn), and additivity, the Leibniz rule and the zero on constants pass through "+
			"h since D's values lie in N's carrier and u, v in S's (HomAdd, HomSmul, HomZero)"),
})}

// KaehlerUniversalExists — every derivation D of S over R into a module
// N over S factors through the differentials: a homomorphism h out of
// Ω_{S/R} with h(du) = D(u).
var KaehlerUniversalExists = kaehlerUniversalExistsThm{family.Add(registry.ProofEntry{
	Name: "KaehlerUniversalExists",
	Key:  "prop_c6f6613f59659416",
	Deps: []registry.EntryLike{
		partial_derivative.DerivationOn,
		KaehlerModuleDef,
		UniversalDerivationDef,
		KaehlerRelationsDef,
		KaehlerRelationsSubmodule,
		KaehlerModuleOn,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		free_module.FreeModuleOn,
		submodule.SpanLeast,
		submodule.QuotientSmulCoset,
		module_homomorphism.KernelSubmodule,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		module_homomorphism.HomSmul,
		equivalence.InducedMapDef,
		quotient_group.LeftCosetMulOn,
		quotient_group.InLeftCosets,
		set_basic.InUnion,
		ring_homomorphism.Target,
	},
	Build: family.Card(
		partial_derivative.DerivationOn.Statement(
			"∃h:(set(B → B) → C). "+
				"    module_homomorphism(S, kaehler_module(R, S, f), N, h) ∧ "+
				"    (∀u:B. u ∈ S.carrier ⇒ h(universal_derivation(R, S, f, u)) = D(u))"),
		"F = free_lift(S.zero, N.add, N.zero, N.smul, D) is a homomorphism out of the free "+
			"module on S's carrier (FreeLiftHom) with F(δ_u) = D(u) (FreeLiftDelta); additivity, "+
			"the Leibniz rule and D(f(a)) = N.zero put every relation element in its kernel, a "+
			"submodule (KernelSubmodule, HomAdd, HomNeg, HomSmul), hence the relations "+
			"(SpanLeast); h = induced_map(F) reads F at a member of the coset, well defined "+
			"since two members differ by a relation (InducedMapDef), and is a homomorphism by "+
			"LeftCosetMulOn and QuotientSmulCoset — the route of tensor_product's TensorUniversal"),
})}

// KaehlerUniversalUnique — two homomorphisms out of the differentials
// that agree on every du agree on the module; with KaehlerUniversalExists,
// the homomorphism a derivation factors through is unique.
var KaehlerUniversalUnique = kaehlerUniversalUniqueThm{family.Add(registry.ProofEntry{
	Name: "KaehlerUniversalUnique",
	Key:  "prop_8c95586e0ecd0216",
	Deps: []registry.EntryLike{
		KaehlerSpan,
		KaehlerModuleOn,
		module_homomorphism.HomDiff,
		module_homomorphism.KernelSubmodule,
		submodule.SpanLeast,
		group.RightInverseOn,
		group.InvUniqueOn,
		module.AddGroupOn,
		set_basic.InImage,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, C). " +
			"∀h h':(set(B → B) → C). " +
			"∀t:set(B → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"module_homomorphism(S, kaehler_module(R, S, f), N, h)",
			"module_homomorphism(S, kaehler_module(R, S, f), N, h')",
			"∀u:B. u ∈ S.carrier ⇒ h(universal_derivation(R, S, f, u)) = h'(universal_derivation(R, S, f, u))",
			"t ∈ kaehler_module(R, S, f).carrier",
		},
		Conclusion: "h(t) = h'(t)",
	},
		"the vectors where h and h' agree are the kernel of their difference, a "+
			"homomorphism (HomDiff), so a submodule (KernelSubmodule) holding every "+
			"du; it holds their span (SpanLeast), which is the carrier (KaehlerSpan)"),
	Reading: "The agreement is asked on the differentials of S's carrier only and concluded " +
		"on Ω's carrier only; off the carrier the two maps are unconstrained. Applied to h and " +
		"h' that both carry du to D(u) it is the uniqueness of the factorization, so with " +
		"KaehlerUniversalExists and DerivationComposeHomomorphism h ↦ h ∘ d is a bijection from " +
		"the homomorphisms out of Ω_{S/R} onto the derivations, read on the carriers.",
})}

// ---------------------------------------------------------------------------
// The free algebra and the first exact sequence
// ---------------------------------------------------------------------------

// KaehlerFreeAlgebra — the differentials of the free algebra on X are
// the free module on X over the algebra, du going to its partial
// derivatives (∂_x u)_{x ∈ X}.
var KaehlerFreeAlgebra = kaehlerFreeAlgebraThm{family.Add(registry.ProofEntry{
	Name: "KaehlerFreeAlgebra",
	Key:  "prop_40e0b0d268ba26e2",
	Deps: []registry.EntryLike{
		KaehlerUniversalExists,
		KaehlerUniversalUnique,
		UniversalDerivationIsDerivation,
		DerivationComposeHomomorphism,
		KaehlerSpan,
		KaehlerModuleOn,
		partial_derivative.DerivationOn,
		partial_derivative.FreeAlgebraPartialDef,
		free_algebra.FreeAlgebraRingDef,
		free_algebra.FreeAlgebraConstDef,
		free_algebra.FreeAlgebraEmbeddingDef,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		free_module.FreeLiftUnique,
		free_module.FreeModuleOn,
		free_module.DeltaAtIn,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
		module_homomorphism.HomIdentity,
		partial_derivative.PartialIn,
		partial_derivative.PartialSupportFinite,
		partial_derivative.PartialAdd,
		partial_derivative.PartialLeibniz,
		partial_derivative.PartialConst,
		partial_derivative.PartialVar,
		partial_derivative.DerivationUniqueOnGenerators,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraConstHom,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀X:set(D).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
		},
		Conclusion: "∃h:(set(E → E) → D → E). " +
			"    module_isomorphism(free_algebra_ring(ι, R, X), " +
			"        «freeOmega», " +
			"        free_module_record(free_algebra_ring(ι, R, X), X), " +
			"        h) ∧ " +
			"    (∀u:E. " +
			"        u ∈ free_algebra(ι, R, X) ⇒ " +
			"        h(universal_derivation(R, free_algebra_ring(ι, R, X), free_algebra_const(ι, R), u)) = " +
			"        λx:D. free_algebra_partial(ι, R, x, u))",
		Abbrev: Abbrev{
			{Name: "freeOmega", Text: "kaehler_module(R, " +
				"    free_algebra_ring(ι, R, X), " +
				"    free_algebra_const(ι, R))"},
		},
	},
		"u ↦ (λx. ∂_x u) is a derivation into the free module on X over the algebra, which is a "+
			"commutative ring (the free algebra's FreeAlgebraCommRingOn): its values are finitely "+
			"supported and zero off X (partial_derivative's PartialIn, PartialSupportFinite), it is "+
			"additive and Leibniz and zero on constants (PartialAdd, PartialLeibniz, PartialConst); "+
			"KaehlerUniversalExists gives h. The inverse is the free lift of x ↦ d(var x) "+
			"(FreeLiftHom); h sends d(var x) to the generator at x (PartialVar, FreeLiftDelta), so "+
			"the composite on the free module fixes the generators (FreeLiftUnique), and the "+
			"composite on the differentials is a derivation agreeing with d on the variables and "+
			"zero on the constants, hence d itself (DerivationUniqueOnGenerators), so it fixes every "+
			"du and is the identity (KaehlerUniversalUnique). Matsumura, Commutative Ring Theory, §25"),
	Reading: "The value λx. ∂_x u is read at every x of D: off X the derivative of a " +
		"member of the algebra on X is the zero polynomial carried by ι, the algebra's zero, " +
		"so the function lies in the free module on X. Over the zero ring both sides are the " +
		"one-point module, and at X = ∅ the algebra is R's constants and both sides vanish.",
})}

// KaehlerFirstExact — the first fundamental exact sequence, its right
// end: Ω_{S/R} ⊗_S T → Ω_{T/R} → Ω_{T/S} → 0 is exact, the first map
// taking du ⊗ t to t • d(g(u)) and the second taking dt to dt.
var KaehlerFirstExact = kaehlerFirstExactThm{family.Add(registry.ProofEntry{
	Name: "KaehlerFirstExact",
	Key:  "prop_cddb9401430b9cab",
	Deps: []registry.EntryLike{
		KaehlerUniversalExists,
		KaehlerUniversalUnique,
		UniversalDerivationIsDerivation,
		KaehlerSpan,
		KaehlerModuleOn,
		KaehlerModuleDef,
		KaehlerRelationsDef,
		UniversalDerivationDef,
		partial_derivative.DerivationOn,
		tensor_product.TensorUniversal,
		tensor_product.TensorSpan,
		tensor_product.TensorModuleOn,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ProjectionHom,
		module_homomorphism.KernelSubmodule,
		submodule.SpanLeast,
		submodule.SubsetSpan,
		ring_homomorphism.MapIn,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		set_basic.InImage,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "∃α:(set(prod(set(B → B), C) → B) → set(C → C)). ∃β:(set(C → C) → set(C → C)). " +
			"    module_homomorphism(S, " +
			"        tensor_module(S, kaehler_module(R, S, f), «algebraOverS»), " +
			"        «restrictedTR», " +
			"        α) ∧ " +
			"    (∀b:B. ∀t:C. " +
			"        b ∈ S.carrier ∧ t ∈ T.carrier ⇒ " +
			"        α(tensor(S, " +
			"                kaehler_module(R, S, f), " +
			"                «algebraOverS», " +
			"                universal_derivation(R, S, f, b), " +
			"                t)) = " +
			"        «omegaTR».smul(t, universal_derivation(R, T, g ∘ f, g(b)))) ∧ " +
			"    module_homomorphism(T, «omegaTR», kaehler_module(S, T, g), β) ∧ " +
			"    (∀t:C. " +
			"        t ∈ T.carrier ⇒ " +
			"        β(universal_derivation(R, T, g ∘ f, t)) = universal_derivation(S, T, g, t)) ∧ " +
			"    exact_at(kaehler_module(S, T, g).zero, " +
			"        tensor_product(S, kaehler_module(R, S, f), «algebraOverS»), " +
			"        «omegaTR».carrier, " +
			"        α, " +
			"        β) ∧ " +
			"    image(β, «omegaTR».carrier) = kaehler_module(S, T, g).carrier",
		Abbrev: Abbrev{
			{Name: "omegaTR", Text: "kaehler_module(R, T, g ∘ f)"},
			{Name: "algebraOverS", Text: "scalar_restriction(g, regular_module(T))"},
			{Name: "restrictedTR", Text: "scalar_restriction(g, «omegaTR»)"},
		},
	},
		"b ↦ d(g(b)) is a derivation of S over R into the differentials of T with scalars "+
			"restricted along g, so KaehlerUniversalExists gives ψ, and (ω, t) ↦ t • ψ(ω) is bilinear "+
			"over S, giving α (TensorUniversal); the relations of T over R lie among those of T over "+
			"S, so β is the coset map of the larger relations, onto. The relations of T over S add to "+
			"those over R the generators δ_{g(b)}, so the kernel of β is the span over T of the "+
			"d(g(b)) (SpanLeast, SubsetSpan), which is the image of α: a member of the tensor product "+
			"is a finite sum of scaled pure tensors (TensorSpan), each du ⊗ t going to t • d(g(u)), "+
			"and du spans Ω_{S/R} (KaehlerSpan). Matsumura, Commutative Ring Theory, Theorem 25.1"),
	Reading: "The tensor product is the corpus's over the one ring S, with T a module over S " +
		"through g, so α is stated linear over S into the differentials of T over R with their scalars " +
		"restricted along g; its linearity over T is not stated, and exactness reads only the sets and " +
		"the two maps. Its image is nonetheless the full T-span of the d(g(b)), because the pure " +
		"tensors db ⊗ t carry any t. At S = R and f the identity Ω_{S/R} = 0, the tensor product is " +
		"zero, and the statement says β is one-to-one: the two modules of differentials of T coincide.",
})}
