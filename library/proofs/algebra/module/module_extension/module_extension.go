// module_extension.go — extensions of a module M by a module N, read
// through a module F with a linear map ε onto M: the product F ⊕ N is a
// module; the graph of −φ over the kernel K of ε is a submodule for φ
// linear on K, and the quotient is an extension E_φ in which (k, 0) is
// (0, φ(k)); a linear map h from F to N shears F ⊕ N by an automorphism
// carrying the graph of −φ₁ to that of −φ₂ when φ₂ − φ₁ is h on K, so
// that E_{φ₁} ≅ E_{φ₂}. Back from an extension E: a lift s of ε to E
// reads a linear map φ_s on K, (u, n) ↦ s(u) + i(n) maps F ⊕ N onto E
// with kernel the graph of −φ_s, so E_{φ_s} ≅ E, and two lifts differ by
// a linear map into N whose restriction to K is the difference of their
// maps.

package module_extension

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The product and the graph
// ---------------------------------------------------------------------------

// TwistedGraphSubmodule — for φ linear on the kernel of ε, the graph of
// −φ over the kernel is a submodule of F ⊕ N.
var TwistedGraphSubmodule = twistedGraphSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "TwistedGraphSubmodule",
	Key:  "prop_7fbb0c70fadd6789",
	Reading: "No onto is asked and no extension is read: the submodule is built " +
		"from φ alone. Linearity of φ on K is what closes the graph, (x, −φ(x)) + " +
		"(y, −φ(y)) = (x + y, −φ(x + y)) and c • (x, −φ(x)) = (c • x, −φ(c • x)).",
	Deps: []registry.EntryLike{
		TwistedGraphDef,
		module_record.ProductModuleDef,
		module_homomorphism.ProductModuleOn,
		hom_module.HomSetDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.KernelSubmodule,
		module_record.RestrictModuleDef,
		submodule.SubmoduleDef,
		module_homomorphism.HomNeg,
		module.SmulNeg,
		module.AddGroupOn,
		module.AddComm,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀φ:(U → D).",
		Hypotheses: []string{
			"module_homomorphism(R, F, M, ε)",
			"module_on(R, N)",
			"φ ∈ hom_set(R, restrict_module(F, group_kernel(M.zero, F.carrier, ε)), N)",
		},
		Conclusion: "submodule(R, product_module(F, N), «graph»(φ))",
	},
		"unfold submodule at TwistedGraphDef: a member is (x, −φ(x)) with x in K, a pair of "+
			"the carrier, φ's values lying in N (HomSetDef, ModuleHomomorphismDef, InCross). K is "+
			"a submodule (KernelSubmodule), so it holds zero, sums, negatives and multiples; φ(0) "+
			"is N.zero by additivity, so the zero pair is in the graph; (x, −φ(x)) + (y, −φ(y)) = "+
			"(x + y, −φ(x + y)), −(x, −φ(x)) = (−x, −φ(−x)) and c • (x, −φ(x)) = (c • x, −φ(c • "+
			"x)) by φ's laws on K (RestrictModuleDef, HomNeg, SmulNeg, AddGroupOn, AddComm)"),
})}

// GraphModuleExtension — for ε onto and φ linear on its kernel, E_φ =
// (F ⊕ N)/J_φ is an extension of M by N; its projection reads the coset
// of (u, n) as ε(u), and the coset of (k, 0) for k in the kernel is the
// inclusion of φ(k).
var GraphModuleExtension = graphModuleExtensionThm{family.Add(registry.ProofEntry{
	Name: "GraphModuleExtension",
	Key:  "prop_cfd5cf9a21f9fcb6",
	Reading: "ε onto is load-bearing for the projection being onto M. φ(0) = N.zero " +
		"makes the inclusion injective. The last conjunct is [(k, 0)] = [(0, φ(k))]: their " +
		"difference (k, −φ(k)) is a pair of the graph. It is how the extension reads φ " +
		"back: the lift u ↦ [(u, 0)] carries k in the kernel to the inclusion of φ(k).",
	Deps: []registry.EntryLike{
		ModuleExtensionGraphDef,
		ModuleExtension,
		TwistedGraphSubmodule,
		TwistedGraphDef,
		module_homomorphism.ProductModuleOn,
		module_record.ProductModuleDef,
		submodule.QuotientModuleOn,
		submodule.QuotientModuleDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ModuleHomomorphismDef,
		equivalence.InducedMapDef,
		quotient_group.InLeftCosets,
		hom_module.HomSetDef,
		functions.InjectiveOnDef,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀φ:(U → D).",
		Hypotheses: []string{
			"module_homomorphism(R, F, M, ε)",
			"module_on(R, N)",
			"image(ε, F.carrier) = M.carrier",
			"φ ∈ hom_set(R, restrict_module(F, group_kernel(M.zero, F.carrier, ε)), N)",
		},
		Conclusion: "module_extension(R, M, N, «extension»(φ)) ∧ " +
			"(∀u:U. ∀n:D. " +
			"    u ∈ F.carrier ∧ n ∈ N.carrier ⇒ " +
			"    «extension»(φ).projection(left_coset(product_module(F, N).add, (u, n), «graph»(φ))) = " +
			"    ε(u)) ∧ " +
			"(∀x:U. " +
			"    x ∈ group_kernel(M.zero, F.carrier, ε) ⇒ " +
			"    left_coset(product_module(F, N).add, (x, N.zero), «graph»(φ)) = " +
			"    «extension»(φ).inclusion(φ(x)))",
	},
		"J_φ is a submodule (TwistedGraphSubmodule), so the cosets are a module and the projection "+
			"onto them linear (QuotientModuleOn, ProjectionHom). Two pairs are in one coset when they "+
			"differ by (k, −φ(k)), k in K (TwistedGraphDef), so ε of the first component is one value on a "+
			"coset and the chosen member gives it (InducedMapDef): the projection is linear and onto, as ε "+
			"is. The inclusion is the projection after n ↦ (0, n) (module_homomorphism.ProductModuleOn), "+
			"linear; it is injective, (0, n − m) in J_φ forcing k = 0 and n − m = −φ(0) = N.zero; its "+
			"image is the kernel of the projection, a coset [(u, n)] with ε(u) = M.zero being [(0, n + "+
			"φ(u))] (ExactAtDef, ShortExactModules). The last conjunct: (k, 0) − (0, φ(k)) is in J_φ"),
})}

// ---------------------------------------------------------------------------
// The shear by a linear map
// ---------------------------------------------------------------------------

// ShearModuleExtensionIso — for h linear from F to N, the shear
// (u, n) ↦ (u, n − h(u)) is an automorphism of F ⊕ N with inverse the
// shear by −h, fixing the pairs (0, n); when φ₂ − φ₁ is h on the kernel
// it carries J_{φ₁} onto J_{φ₂}, and the map it induces on cosets is an
// isomorphism of the extensions E_{φ₁} ≅ E_{φ₂}, the coset of z going to
// the coset of the shear of z.
var ShearModuleExtensionIso = shearModuleExtensionIsoThm{family.Add(registry.ProofEntry{
	Name: "ShearModuleExtensionIso",
	Key:  "prop_b3b80256fc0a99b4",
	Reading: "No onto is asked: the isomorphism is one of the records whether or " +
		"not they are extensions. The sign: the shear carries (k, −φ₁(k)) to (k, " +
		"−φ₁(k) − h(k)) = (k, −φ₂(k)). The isomorphism is the map induced by the shear " +
		"followed by the projection, so its value at every coset is known; the module " +
		"FirstIsomorphism theorem at that composite gives it, its kernel being J_{φ₁}.",
	Deps: []registry.EntryLike{
		DerivationShearDef,
		TwistedGraphDef,
		TwistedGraphSubmodule,
		module_homomorphism.ProductModuleOn,
		module_record.ProductModuleDef,
		ModuleExtensionGraphDef,
		ModuleExtensionIsomorphismDef,
		module_homomorphism.FirstIsomorphism,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ProjectionKernel,
		module_homomorphism.HomCompose,
		module_record.RestrictModuleDef,
		module_record.ModuleOpsData.Ext,
		submodule.QuotientModuleDef,
		equivalence.InducedMapDef,
		quotient_group.InLeftCosets,
		hom_module.HomSetDef,
		functions.InjectiveOnDef,
		module.SmulAddLeft,
		module.SmulNeg,
		module.AddGroupOn,
		module.AddComm,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀φ₁ φ₂ h:(U → D).",
		Hypotheses: []string{
			"module_homomorphism(R, F, M, ε)",
			"module_on(R, N)",
			"φ₁ ∈ hom_set(R, restrict_module(F, group_kernel(M.zero, F.carrier, ε)), N)",
			"φ₂ ∈ hom_set(R, restrict_module(F, group_kernel(M.zero, F.carrier, ε)), N)",
			"h ∈ hom_set(R, F, N)",
			"fun_add(φ₂, fun_neg(φ₁)) = λx:U. COND(x ∈ group_kernel(M.zero, F.carrier, ε), h(x), N.zero)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    product_module(F, N), " +
			"    product_module(F, N), " +
			"    derivation_shear(N, h)) ∧ " +
			"(∀z:prod(U, D). " +
			"    z ∈ product_module(F, N).carrier ⇒ " +
			"    derivation_shear(N, λu:U. N.neg(h(u)), derivation_shear(N, h, z)) = z ∧ " +
			"    derivation_shear(N, h, derivation_shear(N, λu:U. N.neg(h(u)), z)) = z) ∧ " +
			"(∀n:D. n ∈ N.carrier ⇒ derivation_shear(N, h, (F.zero, n)) = (F.zero, n)) ∧ " +
			"image(derivation_shear(N, h), «graph»(φ₁)) = «graph»(φ₂) ∧ " +
			"module_extension_isomorphism(R, " +
			"    N, " +
			"    «extension»(φ₁), " +
			"    «extension»(φ₂), " +
			"    induced_map(λz:prod(U, D). " +
			"            left_coset(product_module(F, N).add, derivation_shear(N, h, z), «graph»(φ₂)))) ∧ " +
			"(∀z:prod(U, D). " +
			"    z ∈ product_module(F, N).carrier ⇒ " +
			"    induced_map(λz':prod(U, D). " +
			"            left_coset(product_module(F, N).add, derivation_shear(N, h, z'), «graph»(φ₂)), " +
			"        left_coset(product_module(F, N).add, z, «graph»(φ₁))) = " +
			"    left_coset(product_module(F, N).add, derivation_shear(N, h, z), «graph»(φ₂)))",
	},
		"the shear: unfold DerivationShearDef and ProductModuleDef at pairs (Fst, Snd); it keeps the "+
			"carrier, h landing in N (HomSetDef), and keeps sums and multiples by h's linearity "+
			"(SmulAddLeft, SmulNeg, AddGroupOn, AddComm); the shears by h and −h undo each other, n − "+
			"h(u) + h(u) = n, so it is a bijection (InjectiveOnDef, ModuleIsomorphismDef); h(0) = N.zero "+
			"fixes (0, n). The image: at k in K the shear of (k, −φ₁(k)) is (k, −φ₂(k)), the hypothesis "+
			"read at k (TwistedGraphDef); both graphs are indexed by K, so the image is J_{φ₂}. The "+
			"composite of the shear and the projection onto the cosets of J_{φ₂} is linear and onto "+
			"(HomCompose, ProjectionHom) with kernel J_{φ₁} (ProjectionKernel, the shear injective), so "+
			"FirstIsomorphism gives the module isomorphism and its value on cosets (InducedMapDef), "+
			"restrict_module of the cosets to all of them being the quotient itself (RestrictModuleDef, "+
			"ModuleOpsEq). The identity on N and over M: the shear fixes (0, n) and the first component, "+
			"which the projection reads (ModuleExtensionGraphDef, InducedMapDef, InLeftCosets)"),
})}

// ---------------------------------------------------------------------------
// Back from an extension: lifts and the map on the kernel they read
// ---------------------------------------------------------------------------

// LiftExtractSyzygy — a lift s of ε to an extension of M by N reads a
// homomorphism φ_s(k) = i⁻¹(s(k)) from the kernel of ε to N.
var LiftExtractSyzygy = liftExtractSyzygyThm{family.Add(registry.ProofEntry{
	Name: "LiftExtractSyzygy",
	Key:  "prop_3dbc8fd95cbcb02c",
	Reading: "p ∘ s = ε puts s(K) in the kernel of the projection, the " +
		"image of N; injectivity of the inclusion makes the preimage unique, " +
		"so additivity and linearity are read through i. No onto is asked of ε.",
	Deps: []registry.EntryLike{
		ExtractSyzygyMapDef,
		ModuleExtension,
		ModuleExtensionLiftDef,
		hom_module.HomSetDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.KernelSubmodule,
		module_record.RestrictModuleDef,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀s:(U → C).",
		Hypotheses: []string{
			"module_homomorphism(R, F, M, ε)",
			"module_on(R, N)",
			"module_extension(R, M, N, E)",
			"«lift»(s)",
		},
		Conclusion: "«extract»(s) ∈ hom_set(R, restrict_module(F, group_kernel(M.zero, F.carrier, ε)), N)",
	},
		"for k in K, p(s(k)) = ε(k) = M.zero (ModuleExtensionLiftDef), so s(k) is in the kernel "+
			"of the projection, the image of N's carrier (ModuleExtension, ShortExactModules, "+
			"ExactAtDef): a preimage exists and inverse_on chooses one in N's carrier (InverseOnIn, "+
			"InverseOnRight). K is a submodule (KernelSubmodule), so restrict_module(F, K) is a "+
			"module (RestrictModuleDef); i(φ_s(k) + φ_s(k')) = s(k) + s(k') = s(k + k') and i(c • "+
			"φ_s(k)) = c • s(k) = s(c • k), so injectivity of i gives additivity and linearity "+
			"(InjectiveOnDef). Off K the value is N.zero (ExtractSyzygyMapDef, HomSetDef)"),
})}

// LiftSumQuotientIso — for ε onto and a lift s, (u, n) ↦ s(u) + i(n) is a
// homomorphism from F ⊕ N onto the extension's module with kernel the
// graph of −φ_s, and the map it induces on cosets is an isomorphism
// E_{φ_s} ≅ E of extensions, the coset of (u, n) going to s(u) + i(n).
var LiftSumQuotientIso = liftSumQuotientIsoThm{family.Add(registry.ProofEntry{
	Name: "LiftSumQuotientIso",
	Key:  "prop_4810b74755777d23",
	Reading: "ε onto is load-bearing for onto: e − s(u), for u with ε(u) = p(e), lies in the " +
		"kernel of the projection, the image of N. (u, n) is in the kernel exactly when s(u) = " +
		"i(−n): then ε(u) = p(s(u)) = M.zero, u in K, and −n = φ_s(u) by injectivity. The " +
		"isomorphism is FirstIsomorphism's named induced map, so its value on every coset is known.",
	Deps: []registry.EntryLike{
		module_homomorphism.ProductModuleOn,
		module_record.ProductModuleDef,
		LiftExtractSyzygy,
		ExtractSyzygyMapDef,
		TwistedGraphDef,
		ModuleExtensionGraphDef,
		ModuleExtensionIsomorphismDef,
		ModuleExtension,
		ModuleExtensionLiftDef,
		module_homomorphism.FirstIsomorphism,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomAdd,
		module_homomorphism.HomSmul,
		module_homomorphism.HomNeg,
		module_record.RestrictModuleDef,
		module_record.ModuleOpsData.Ext,
		equivalence.InducedMapDef,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
		module.AddGroupOn,
		module.AddComm,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀s:(U → C).",
		Hypotheses: []string{
			"module_homomorphism(R, F, M, ε)",
			"module_on(R, N)",
			"image(ε, F.carrier) = M.carrier",
			"module_extension(R, M, N, E)",
			"«lift»(s)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    product_module(F, N), " +
			"    E.module, " +
			"    λz:prod(U, D). E.module.add(s(fst(z)), E.inclusion(snd(z)))) ∧ " +
			"image(λz:prod(U, D). E.module.add(s(fst(z)), E.inclusion(snd(z))), " +
			"    product_module(F, N).carrier) = " +
			"E.module.carrier ∧ " +
			"group_kernel(E.module.zero, " +
			"    product_module(F, N).carrier, " +
			"    λz:prod(U, D). E.module.add(s(fst(z)), E.inclusion(snd(z)))) = " +
			"«graph»(«extract»(s)) ∧ " +
			"module_extension_isomorphism(R, " +
			"    N, " +
			"    «extension»(«extract»(s)), " +
			"    E, " +
			"    induced_map(λz:prod(U, D). E.module.add(s(fst(z)), E.inclusion(snd(z))))) ∧ " +
			"(∀z:prod(U, D). " +
			"    z ∈ product_module(F, N).carrier ⇒ " +
			"    induced_map(λz:prod(U, D). E.module.add(s(fst(z)), E.inclusion(snd(z))), " +
			"        left_coset(product_module(F, N).add, z, «graph»(«extract»(s)))) = " +
			"    (λz:prod(U, D). E.module.add(s(fst(z)), E.inclusion(snd(z))))(z))",
	},
		"F ⊕ N is a module (module_homomorphism.ProductModuleOn); the sum map lands in E's module "+
			"and keeps sums and multiples, s and i doing so and E's addition being commutative and "+
			"associative (HomAdd, HomSmul, AddComm, AddGroupOn, ModuleHomomorphismDef). Onto: for e in "+
			"E's module take u in F with ε(u) = p(e) (onto); e − s(u) has projection zero, so it is "+
			"i(n) for some n in N's carrier (ShortExactModules, ExactAtDef), and e = s(u) + i(n). The "+
			"kernel: s(u) + i(n) = 0 gives ε(u) = p(s(u)) = −p(i(n)) = M.zero, so u is in K and s(u) = "+
			"i(φ_s(u)) (ExtractSyzygyMapDef, InverseOnRight), so i(φ_s(u) + n) = 0 and n = −φ_s(u) by "+
			"injectivity; conversely s(k) + i(−φ_s(k)) = 0 (TwistedGraphDef, HomNeg). FirstIsomorphism "+
			"at the sum map gives the isomorphism of the quotient by its kernel onto restrict_module "+
			"of E's module to the image, which is E's module itself (RestrictModuleDef, ModuleOpsEq), "+
			"and its value on cosets (InducedMapDef). On N: [(0, n)] goes to s(0) + i(n) = i(n); over "+
			"M: p(s(u) + i(n)) = ε(u), the graph's projection at [(u, n)]"),
})}

// LiftDifferenceHom — two lifts s₁, s₂ of ε to an extension differ by
// i ∘ h for one homomorphism h from F to N, and φ_{s₂} − φ_{s₁} is h on
// the kernel of ε.
var LiftDifferenceHom = liftDifferenceHomThm{family.Add(registry.ProofEntry{
	Name: "LiftDifferenceHom",
	Key:  "prop_18e3ebbc4d3d312b",
	Reading: "h(u) = i⁻¹(s₂(u) − s₁(u)), N.zero off F: the difference has " +
		"projection ε(u) − ε(u) = M.zero, so it lies in the image of N. hom_set asks " +
		"h to be N.zero off F, which makes it unique as a function. No onto is asked.",
	Deps: []registry.EntryLike{
		ModuleExtension,
		ModuleExtensionLiftDef,
		ExtractSyzygyMapDef,
		LiftExtractSyzygy,
		hom_module.HomSetDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomDiff,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		functions.InverseOnIn,
		functions.InverseOnRight,
		functions.InjectiveOnDef,
		module.AddGroupOn,
		module.AddComm,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, D). " +
			"∀F:module_ops(A, U). " +
			"∀ε:(U → B). " +
			"∀E:module_extension_ops(A, B, C, D). " +
			"∀s₁ s₂:(U → C).",
		Hypotheses: []string{
			"module_homomorphism(R, F, M, ε)",
			"module_on(R, N)",
			"module_extension(R, M, N, E)",
			"«lift»(s₁)",
			"«lift»(s₂)",
		},
		Conclusion: "∃h:(U → D). " +
			"    h ∈ hom_set(R, F, N) ∧ " +
			"    (∀u:U. u ∈ F.carrier ⇒ E.module.add(s₂(u), E.module.neg(s₁(u))) = E.inclusion(h(u))) ∧ " +
			"    fun_add(«extract»(s₂), fun_neg(«extract»(s₁))) = " +
			"    (λx:U. COND(x ∈ group_kernel(M.zero, F.carrier, ε), h(x), N.zero)) ∧ " +
			"    (∀h':(U → D). " +
			"        h' ∈ hom_set(R, F, N) ∧ " +
			"        (∀u:U. u ∈ F.carrier ⇒ E.module.add(s₂(u), E.module.neg(s₁(u))) = E.inclusion(h'(u))) ⇒ " +
			"        h' = h)",
	},
		"take h(u) = inverse_on(N.carrier, i, s₂(u) − s₁(u)) on F's carrier and N.zero off "+
			"it: the difference is linear (HomDiff) with projection ε(u) − ε(u) = M.zero "+
			"(ModuleExtensionLiftDef), so it is in the image of N's carrier and h(u) its preimage "+
			"there (ShortExactModules, ExactAtDef, InverseOnIn, InverseOnRight). h is linear, "+
			"i(h(u) + h(v)) = i(h(u + v)) and likewise for multiples, by injectivity of i "+
			"(InjectiveOnDef, HomSetDef). On K, φ_{s₂}(k) − φ_{s₁}(k) = i⁻¹(s₂(k)) − i⁻¹(s₁(k)) = "+
			"h(k) by injectivity (ExtractSyzygyMapDef); off K both sides are N.zero. Uniqueness: "+
			"two such maps agree on F's carrier by injectivity of i, and both are N.zero off it"),
})}
