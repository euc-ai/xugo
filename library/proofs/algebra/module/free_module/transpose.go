// transpose.go — the transpose of a linear map between free modules,
// hom_precompose with coefficients in a module N: for Φ from the free
// module on S to the free module on S', a function u on the target
// generators goes to s ↦ Σ_t Φ(δ_s)(t) • u(t) on S, and to N.zero off S.
// The pairing of a free-module element v with an N-valued function u is
// free_lift(R.zero, N.add, N.zero, N.smul, u, v). The transpose is linear
// between the function modules, adjoint to Φ under the pairing, reads Φ
// only on the free module, reverses composites, is linear in Φ and
// commutes with a linear map of coefficient modules: the laws every
// statement about the dual complex reduces to.

package free_module

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// HomPrecomposeDef — `hom_precompose(R, N, S, Φ, u, x)`: the transpose
// of Φ with coefficients in N, applied to a function u on the target
// basis set and read at x. For x in S it is the pairing of u with
// Φ(δ_x), free_lift(R.zero, N.add, N.zero, N.smul, u, Φ(δ_x)) =
// Σ_t Φ(δ_x)(t) • u(t); off S it is N.zero.
var HomPrecomposeDef = homPrecomposeDefThm{family.Define(registry.DefEntry{
	Name:  "HomPrecomposeDef",
	Const: "hom_precompose",
	Type:  "ring_ops(A) → module_ops(A, D) → set(I) → ((I → A) → E → A) → (E → D) → I → D",
	Key:   "prop_2204f59b6e9b2549",
	Equations: []string{
		"∀R:ring_ops(A). ∀N:module_ops(A, D). ∀S:set(I). ∀Φ:((I → A) → E → A). ∀u:(E → D). ∀x:I. " +
			"    hom_precompose(R, N, S, Φ, u, x) = " +
			"    COND(x ∈ S, " +
			"        free_lift(R.zero, N.add, N.zero, N.smul, u, Φ(delta_at(R.zero, R.one, x))), " +
			"        N.zero)",
	},
	Deps: []registry.EntryLike{FreeLiftDef, DeltaAtDef},
})}

// ---------------------------------------------------------------------------
// The transpose of one map
// ---------------------------------------------------------------------------

// HomPrecomposeHom — the transpose of a linear map of free modules is
// linear between the function modules.
var HomPrecomposeHom = homPrecomposeHomThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposeHom",
	Key:  "prop_fc5d68b8914ce9dd",
	Reading: "Of Φ only that it carries each generator δ_s, s ∈ S, into finite_supp(R.zero, " +
		"R.carrier, S') is read; linearity of Φ is asked because every consumer has it.",
	Deps: []registry.EntryLike{
		HomPrecomposeDef,
		function_module.FunctionModuleDef,
		function_module.FunModuleDef,
		function_module.FunModuleOn,
		HomDeltaIn,
		FreeLiftHom,
		FreeLiftMapLinear,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:set(I). ∀S':set(E). ∀Φ:((I → A) → E → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"«transposeFreeMap»",
		},
		Conclusion: "module_homomorphism(R, " +
			"    function_module(N, S'), " +
			"    function_module(N, S), " +
			"    hom_precompose(R, N, S, Φ))",
	},
		"Both function modules are modules (FunModuleOn). At s ∈ S the value is free_lift of u at "+
			"Φ(δ_s), a member of the free module on S' (HomDeltaIn), in N's carrier (FreeLiftHom, u's "+
			"values on S' in the carrier), and N.zero off S: the transpose lands in fun_module(N.zero, "+
			"N.carrier, S). It is linear in u pointwise by FreeLiftMapLinear, function_module's "+
			"operations being pointwise (FunctionModuleDef); off S both sides of each law are N.zero."),
})}

// HomPrecomposePairing — the transpose is adjoint to Φ under the pairing
// free_lift: ⟨Φ(v), u⟩ = ⟨v, Φᵗ(u)⟩.
var HomPrecomposePairing = homPrecomposePairingThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposePairing",
	Key:  "prop_b264abfe9b61ff43",
	Deps: []registry.EntryLike{
		HomPrecomposeHom,
		HomPrecomposeDef,
		FreeLiftHom,
		FreeLiftDelta,
		FreeLiftUnique,
		DeltaAtIn,
		module_homomorphism.HomCompose,
		module_homomorphism.HomIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:set(I). " +
			"∀S':set(E). " +
			"∀Φ:((I → A) → E → A). " +
			"∀v:(I → A). " +
			"∀u:(E → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"«transposeFreeMap»",
			"v ∈ finite_supp(R.zero, R.carrier, S)",
			"u ∈ fun_module(N.zero, N.carrier, S')",
		},
		Conclusion: "free_lift(R.zero, N.add, N.zero, N.smul, u, Φ(v)) = " +
			"free_lift(R.zero, N.add, N.zero, N.smul, hom_precompose(R, N, S, Φ, u), v)",
	},
		"Both sides are linear in v on the free module on S: the left as free_lift (FreeLiftHom) "+
			"after Φ (HomCompose), the right by FreeLiftHom, the transpose's values on S in N's "+
			"carrier (HomPrecomposeHom, HomIn). At a generator δ_s the right side is the transpose "+
			"at s (FreeLiftDelta), which is the left side by HomPrecomposeDef; FreeLiftUnique closes."),
})}

// HomPrecomposeCongruence — the transpose reads a map only on the free
// module: two maps equal there have one transpose.
var HomPrecomposeCongruence = homPrecomposeCongruenceThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposeCongruence",
	Key:  "prop_5d4fffd46b8078cb",
	Reading: "No hypothesis on u: the two total functions " +
		"are equal. module_on(R, N) is read only for the ring.",
	Deps: []registry.EntryLike{HomPrecomposeDef, DeltaAtIn, module.RingOn},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:set(I). ∀Φ Ψ:((I → A) → E → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"∀a:(I → A). a ∈ finite_supp(R.zero, R.carrier, S) ⇒ Φ(a) = Ψ(a)",
		},
		Conclusion: "hom_precompose(R, N, S, Φ) = hom_precompose(R, N, S, Ψ)",
	},
		"Extensionality in u and s: at s ∈ S both read the map at δ_s, a member "+
			"of the free module on S (DeltaAtIn, the commutative ring of module_on, "+
			"RingOn), where the maps agree; off S both are N.zero (HomPrecomposeDef)."),
})}

// ---------------------------------------------------------------------------
// Composites, combinations of maps and change of coefficients
// ---------------------------------------------------------------------------

// HomPrecomposeIdentity — the identity transposes to the identity on the
// function module.
var HomPrecomposeIdentity = homPrecomposeIdentityThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposeIdentity",
	Key:  "prop_7e1f1335868be337",
	Deps: []registry.EntryLike{HomPrecomposeDef, function_module.FunModuleDef, FreeLiftDelta},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:set(I). ∀u:(I → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"u ∈ fun_module(N.zero, N.carrier, S)",
		},
		Conclusion: "hom_precompose(R, N, S, λa:(I → A). a, u) = u",
	},
		"at s ∈ S, free_lift of u at δ_s is u(s) (FreeLiftDelta); "+
			"off S both are N.zero, u being zero off S (FunModuleDef)"),
})}

// HomPrecomposeCompose — a composite transposes to the reversed composite
// of the transposes.
var HomPrecomposeCompose = homPrecomposeComposeThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposeCompose",
	Key:  "prop_f2d8bb3e7ecd492b",
	Deps: []registry.EntryLike{HomPrecomposeDef, HomDeltaIn, HomPrecomposePairing},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:set(I). " +
			"∀S':set(E). " +
			"∀S'':set(F). " +
			"∀Φ:((I → A) → E → A). " +
			"∀Ψ:((E → A) → F → A). " +
			"∀u:(F → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"«transposeFreeMap»",
			"module_homomorphism(R, free_module_record(R, S'), free_module_record(R, S''), Ψ)",
			"u ∈ fun_module(N.zero, N.carrier, S'')",
		},
		Conclusion: "hom_precompose(R, N, S, λa:(I → A). Ψ(Φ(a)), u) = " +
			"hom_precompose(R, N, S, Φ, hom_precompose(R, N, S', Ψ, u))",
	},
		"at s ∈ S the left side is free_lift of u at Ψ(Φ(δ_s)), which HomPrecomposePairing at "+
			"Ψ and v = Φ(δ_s), a member of the free module on S' (HomDeltaIn), turns into "+
			"free_lift of Ψᵗ(u) at Φ(δ_s), the right side; off S both are N.zero (HomPrecomposeDef)"),
})}

// HomPrecomposeLinear — the transpose is linear in the map: zero, sums,
// negatives, scalings and finite combinations.
var HomPrecomposeLinear = homPrecomposeLinearThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposeLinear",
	Key:  "prop_ba65a873512f65c3",
	Reading: "The finite combination is the shape of an alternating face sum Σ_i (−1)^i " +
		"J(d_i), whose transpose is Σ_i (−1)^i J(d_i)ᵗ without expanding the sum in the proof that " +
		"reads it. The maps need not be linear, only carry the free module on S into the one on S'.",
	Deps: []registry.EntryLike{
		HomPrecomposeDef,
		FreeLiftDef,
		FreeLiftHom,
		FreeModuleOn,
		FreeModuleRecordDef,
		DeltaAtIn,
		function_module.ModuleSumApply,
		function_module.FunAddDef,
		function_module.FunZeroDef,
		function_module.FunNegDef,
		function_module.FunSmulDef,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		module_homomorphism.HomSmul,
		module.ModuleSumEmpty,
		module.ModuleSumInsert,
		module.SmulZero,
		module.RingOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:set(I). ∀S':set(E). ∀u:(E → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"u ∈ fun_module(N.zero, N.carrier, S')",
		},
		Conclusion: "hom_precompose(R, N, S, λa:(I → A). fun_zero⟨D:E⟩(R.zero), u) = " +
			"fun_zero⟨D:I⟩(N.zero) ∧ " +
			"(∀Φ Ψ:((I → A) → E → A). " +
			"    (∀a:(I → A). " +
			"        a ∈ finite_supp(R.zero, R.carrier, S) ⇒ " +
			"        Φ(a) ∈ finite_supp(R.zero, R.carrier, S') ∧ " +
			"        Ψ(a) ∈ finite_supp(R.zero, R.carrier, S')) ⇒ " +
			"    hom_precompose(R, N, S, λa:(I → A). fun_add⟨D:E⟩(R.add, Φ(a), Ψ(a)), u) = " +
			"    fun_add⟨D:I⟩(N.add, hom_precompose(R, N, S, Φ, u), hom_precompose(R, N, S, Ψ, u)) ∧ " +
			"    hom_precompose(R, N, S, λa:(I → A). fun_neg⟨D:E⟩(R.neg, Φ(a)), u) = " +
			"    fun_neg⟨D:I⟩(N.neg, hom_precompose(R, N, S, Φ, u)) ∧ " +
			"    (∀c:A. " +
			"        c ∈ R.carrier ⇒ " +
			"        hom_precompose(R, N, S, λa:(I → A). fun_smul⟨D:E⟩(R.mul, c, Φ(a)), u) = " +
			"        fun_smul⟨D:I⟩(N.smul, c, hom_precompose(R, N, S, Φ, u)))) ∧ " +
			"(∀K:set(H). ∀φ:(H → (I → A) → E → A). ∀c:(H → A). " +
			"    finite(K) ∧ " +
			"    (∀k:H. " +
			"        k ∈ K ⇒ " +
			"        c(k) ∈ R.carrier ∧ " +
			"        (∀a:(I → A). " +
			"            a ∈ finite_supp(R.zero, R.carrier, S) ⇒ " +
			"            φ(k)(a) ∈ finite_supp(R.zero, R.carrier, S'))) ⇒ " +
			"    hom_precompose(R, " +
			"        N, " +
			"        S, " +
			"        λa:(I → A). " +
			"            module_sum(fun_add⟨D:E⟩(R.add), " +
			"                fun_zero⟨D:E⟩(R.zero), " +
			"                K, " +
			"                λk:H. fun_smul⟨D:E⟩(R.mul, c(k), φ(k)(a))), " +
			"        u) = " +
			"    module_sum(fun_add⟨D:I⟩(N.add), " +
			"        fun_zero⟨D:I⟩(N.zero), " +
			"        K, " +
			"        λk:H. fun_smul⟨D:I⟩(N.smul, c(k), hom_precompose(R, N, S, φ(k), u))))",
	},
		"Pointwise at s ∈ S each side is free_lift of u at the corresponding combination of the "+
			"maps' values at δ_s, members of the free module on S' (DeltaAtIn and the hypothesis), "+
			"and free_lift is linear there in that argument (FreeLiftHom, the combination staying "+
			"in the free module by FreeModuleOn): sums (HomAdd), negatives (HomNeg) and scalings "+
			"(HomSmul) pass through, the finite combination by induction on K (ModuleSumEmpty, "+
			"ModuleSumInsert, ModuleSumApply on both sides, the sums evaluated pointwise). Off S "+
			"both sides are N.zero, every pointwise operation keeping N.zero (SmulZero). The zero "+
			"map: free_lift at the zero function is the empty sum (FreeLiftDef)."),
})}

// HomPrecomposeCoefficientNatural — a linear map of coefficient modules
// commutes with the transpose.
var HomPrecomposeCoefficientNatural = homPrecomposeCoefficientNaturalThm{family.Add(registry.ProofEntry{
	Name: "HomPrecomposeCoefficientNatural",
	Key:  "prop_b57bd46ed2ae1c31",
	Deps: []registry.EntryLike{HomPrecomposeDef, FreeLiftDef, HomDeltaIn, function_module.FunModuleDef,
		module_homomorphism.HomSum, module_homomorphism.HomSmul, module_homomorphism.HomZero},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀N':module_ops(A, D). " +
			"∀k:(C → D). " +
			"∀S:set(I). " +
			"∀S':set(E). " +
			"∀Φ:((I → A) → E → A). " +
			"∀u:(E → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_on(R, N')",
			"module_homomorphism(R, N, N', k)",
			"«transposeFreeMap»",
			"u ∈ fun_module(N.zero, N.carrier, S')",
		},
		Conclusion: "(λx:I. k(hom_precompose(R, N, S, Φ, u, x))) = " +
			"hom_precompose(R, N', S, Φ, λy:E. k(u(y)))",
	},
		"At s ∈ S, k of the finite sum Σ_t Φ(δ_s)(t) • u(t) — finite because Φ(δ_s) lies in the "+
			"free module on S' (HomDeltaIn) — is the sum of Φ(δ_s)(t) • k(u(t)) over the same index set "+
			"(HomSum, HomSmul; HomPrecomposeDef, FreeLiftDef); off S, k(N.zero) = N'.zero (HomZero)."),
})}
