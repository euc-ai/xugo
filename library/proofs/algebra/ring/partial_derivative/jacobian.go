// jacobian.go — the Jacobian of a map Φ from the free algebra on S to
// the free algebra on T: the matrix of the partial derivatives
// ∂_t Φ(var s), its entries carried by a ring map ε into the scalars of
// a module N, applied to the finitely supported functions on S with
// values in N; and its transpose, which pulls the functions on T with
// values in N back along the same matrix. For an algebra map both are
// linear, the Jacobian of a generator is its column, a map fixing the
// variables has the identity as Jacobian, the Jacobian of a composite
// is the composite of the Jacobians (the chain rule), and a map that
// keeps the algebra on part of the variables has a block triangular
// Jacobian.

package partial_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// FreeAlgebraJacobianDef — `free_algebra_jacobian(ι, ι', R, R', S, T, Φ,
// ε, N, u)`: the Jacobian of Φ at u, the function on the variables of T
// whose value at t is Σ_{s ∈ S, u(s) ≠ N.zero} ε(∂_t Φ(var s)) • u(s),
// the variable s taken over R in the host of ι and the derivative over
// R' in the host of ι', and N.zero at t outside T.
var FreeAlgebraJacobianDef = freeAlgebraJacobianDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraJacobianDef",
	Key:   "prop_6d3481c8d7dde665",
	Const: "free_algebra_jacobian",
	Type: "(((D → num) → A) → E) → " +
		"(((I → num) → B) → C) → " +
		"ring_ops(A) → " +
		"ring_ops(B) → " +
		"set(D) → " +
		"set(I) → " +
		"(E → C) → " +
		"(C → F) → " +
		"module_ops(F, G) → " +
		"(D → G) → " +
		"I → " +
		"G",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G). " +
			"∀u:(D → G). " +
			"∀t:I. " +
			"    free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε, N, u, t) = " +
			"    COND(t ∈ T, " +
			"        module_sum(N.add, " +
			"            N.zero, " +
			"            {s:D | s ∈ S ∧ ¬(u(s) = N.zero)}, " +
			"            λs:D. " +
			"                N.smul(ε(free_algebra_partial(ι', R', t, Φ(free_algebra_var(ι, R, s)))), " +
			"                    u(s))), " +
			"        N.zero)",
	},
	Reading: "S selects the columns the sum reads and T the rows it writes: for S and " +
		"T split into parts, the map at a part S₂ of S and a part T₂ of T is the " +
		"restriction to the functions supported on S₂ followed by the projection onto T₂, " +
		"the block of the matrix there. The sum is finite for u of finite support on S, and " +
		"Φ is read only at the variables of S; with Φ carrying the algebra on S into the " +
		"algebra on T, ι' an embedding and R' a commutative ring (PartialSupportFinite), " +
		"every ∂_t Φ(var s) vanishes at t outside T, so the guard on T removes nothing there.",
	Deps: []registry.EntryLike{FreeAlgebraPartialDef},
})}

// FreeAlgebraJacobianTransposeDef — `free_algebra_jacobian_transpose(ι,
// ι', R, R', S, T, Φ, ε, N, w)`: the transpose of the Jacobian at a
// function w on the variables of T, the function on the variables of S
// whose value at s is Σ_{t ∈ T} ε(∂_t Φ(var s)) • w(t), and N.zero at s
// outside S.
var FreeAlgebraJacobianTransposeDef = freeAlgebraJacobianTransposeDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraJacobianTransposeDef",
	Key:   "prop_f82a794b89afee42",
	Const: "free_algebra_jacobian_transpose",
	Type: "(((D → num) → A) → E) → " +
		"(((I → num) → B) → C) → " +
		"ring_ops(A) → " +
		"ring_ops(B) → " +
		"set(D) → " +
		"set(I) → " +
		"(E → C) → " +
		"(C → F) → " +
		"module_ops(F, G) → " +
		"(I → G) → " +
		"D → " +
		"G",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G). " +
			"∀w:(I → G). " +
			"∀s:D. " +
			"    free_algebra_jacobian_transpose(ι, ι', R, R', S, T, Φ, ε, N, w, s) = " +
			"    COND(s ∈ S, " +
			"        module_sum(N.add, " +
			"            N.zero, " +
			"            {t:I | " +
			"                t ∈ T ∧ " +
			"                ¬(N.smul(ε(free_algebra_partial(ι', R', t, Φ(free_algebra_var(ι, R, s)))), " +
			"                        w(t)) = " +
			"                    N.zero)}, " +
			"            λt:I. " +
			"                N.smul(ε(free_algebra_partial(ι', R', t, Φ(free_algebra_var(ι, R, s)))), " +
			"                    w(t))), " +
			"        N.zero)",
	},
	Reading: "w need not have finite support, but the sum is finite when its values on T lie in " +
		"N's carrier: it runs over the t of T where its term is nonzero, finitely many when Φ(var s) is " +
		"a member of the algebra on T, ι' an embedding, R' a commutative ring, ε a ring map, N a module " +
		"and every w(t) in N.carrier, since a zero derivative gives the zero scalar, which sends w(t) " +
		"to N.zero only for w(t) in the carrier; the laws over it ask w ∈ fun_module(N.zero, N.carrier, " +
		"T) for that. A linear map h into N from the finitely supported functions on T over the scalar " +
		"ring, composed with the Jacobian over that ring, sends the generator at s to the transpose at " +
		"w = (t ↦ h(generator at t)), so this is the coboundary on the functions with values in N.",
	Deps: []registry.EntryLike{FreeAlgebraPartialDef},
})}

// ---------------------------------------------------------------------------
// The Jacobian of an algebra map
// ---------------------------------------------------------------------------

// JacobianHom — the Jacobian of an algebra map is a homomorphism from
// the finitely supported functions on S with values in N to those on T.
var JacobianHom = jacobianHomThm{family.Add(registry.ProofEntry{
	Name: "JacobianHom",
	Key:  "prop_108c1df727cd24d1",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianDef,
		PartialIn,
		PartialSupportFinite,
		free_algebra.FreeAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraVarDef,
		function_module.FiniteSuppModuleOn,
		function_module.FiniteSuppModuleDef,
		function_module.FiniteSuppDef,
		module_homomorphism.ModuleHomomorphismDef,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.ModuleSumIn,
		module.ModuleSumSupport,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
		module.SmulAddRight,
		module.SmulMul,
		module.ZeroSmul,
		finite_set.FiniteUnions,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀K:ring_ops(F). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"ring_homomorphism(free_algebra_ring(ι', R', T), K, ε)",
			"module_on(K, N)",
		},
		Conclusion: "module_homomorphism(K, " +
			"    finite_supp_module(N, S), " +
			"    finite_supp_module(N, T), " +
			"    free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε, N))",
	},
		"both records are modules over K (FiniteSuppModuleOn). Each entry ε(∂_t Φ(var s)) lies in "+
			"K's carrier: var s is in the algebra on S (the free algebra's FreeAlgebraVarIn), Φ "+
			"carries it into the algebra on T, PartialIn keeps it there and ε maps into K (MapIn); so "+
			"J(u)(t) is a finite sum in N's carrier (ModuleSumIn). It is nonzero only at t where some "+
			"∂_t Φ(var s), s in the finite support of u, is nonzero, ε keeping zero "+
			"(AdditiveHomomorphism, ZeroSmul): finitely many by PartialSupportFinite and FiniteUnions. "+
			"For u + v and c • u extend each sum to the union of the supports (ModuleSumSupport), then "+
			"ModuleSumAdd with SmulAddRight, and ModuleSumSmul with SmulMul and K commutative"),
})}

// JacobianDelta — the Jacobian of the generator at s with value n is the
// column of s: its value at t is ε(∂_t Φ(var s)) • n.
var JacobianDelta = jacobianDeltaThm{family.Add(registry.ProofEntry{
	Name: "JacobianDelta",
	Key:  "prop_2329720031fc05d8",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianDef,
		free_module.DeltaAtDef,
		PartialIn,
		PartialSupportFinite,
		free_algebra.FreeAlgebraHomomorphismDef,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.ModuleSumEmpty,
		module.ModuleSumInsert,
		module.SmulIn,
		module.SmulZero,
		module.ZeroSmul,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀K:ring_ops(F). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G). " +
			"∀s:D. " +
			"∀t:I. " +
			"∀n:G.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"ring_homomorphism(free_algebra_ring(ι', R', T), K, ε)",
			"module_on(K, N)",
			"s ∈ S",
			"n ∈ N.carrier",
		},
		Conclusion: "free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε, N, delta_at(N.zero, n, s), t) = " +
			"N.smul(ε(free_algebra_partial(ι', R', t, Φ(free_algebra_var(ι, R, s)))), n)",
	},
		"for n ≠ N.zero the sum runs over {s} and is its one term (ModuleSumInsert, "+
			"ModuleSumEmpty, the term in N's carrier by MapIn and SmulIn); for n = N.zero it is empty "+
			"and the right side is a scalar times zero (SmulZero). At t outside T both sides are "+
			"zero: Φ(var s) lies in the algebra on T(var s in the algebra on S by the free algebra's "+
			"FreeAlgebraVarIn), so ∂_t of it is zero (PartialSupportFinite), ε keeps zero and ZeroSmul"),
	Reading: "No hypothesis puts t in T: outside T the guard gives N.zero and the column " +
		"entry is ε of a zero derivative, so the guard removes nothing for an algebra map.",
})}

// JacobianIdentity — a map fixing every variable of S has the identity
// as its Jacobian on the finitely supported functions on S.
var JacobianIdentity = jacobianIdentityThm{family.Add(registry.ProofEntry{
	Name: "JacobianIdentity",
	Key:  "prop_b294b633e5a1ec2d",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianDef,
		PartialVar,
		ring_homomorphism.MapOne,
		ring_homomorphism.AdditiveHomomorphism,
		ring_homomorphism.MapIn,
		module.SmulOne,
		module.ZeroSmul,
		module.ModuleSumSupport,
		module.ModuleSumInsert,
		module.ModuleSumEmpty,
		function_module.FiniteSuppDef,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀S:set(D). " +
			"∀Φ:(E → E). " +
			"∀K:ring_ops(F). " +
			"∀ε:(E → F). " +
			"∀N:module_ops(F, G). " +
			"∀u:(D → G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"comm_ring_on(R)",
			"∀s:D. s ∈ S ⇒ Φ(free_algebra_var(ι, R, s)) = free_algebra_var(ι, R, s)",
			"ring_homomorphism(free_algebra_ring(ι, R, S), K, ε)",
			"module_on(K, N)",
			"u ∈ finite_supp(N.zero, N.carrier, S)",
		},
		Conclusion: "free_algebra_jacobian(ι, ι, R, R, S, S, Φ, ε, N, u) = u",
	},
		"at t ∈ S each entry is ε(∂_t var s), ε of one at s = t and of zero elsewhere "+
			"(PartialVar), K.one and K.zero (MapOne, AdditiveHomomorphism); the sum drops to the term "+
			"at t, K.one • u(t) = u(t) (SmulOne), or is empty when u(t) = N.zero; the host's one and "+
			"zero are those of the algebra on S(the free algebra's "+
			"FreeAlgebraOpsIndependentOfVariables). Outside S both sides are N.zero, u being zero off S"),
	Reading: "Φ need fix only the variables of S: the Jacobian reads Φ there and nowhere else, " +
		"so a composite of faces and degeneracies that is the identity on the algebra on S serves.",
})}

// JacobianCompose — the chain rule for Jacobians: the Jacobian of the
// composite Φ' ∘ Φ at ε is the Jacobian of Φ' at ε after the Jacobian
// of Φ at any ε' that agrees with ε ∘ Φ' on the algebra on T.
var JacobianCompose = jacobianComposeThm{family.Add(registry.ProofEntry{
	Name: "JacobianCompose",
	Key:  "prop_8b8c22f9b8a43171",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianDef,
		ChainRule,
		JacobianHom,
		JacobianCongruence,
		PartialIn,
		PartialSupportFinite,
		free_algebra.FreeAlgebraHomomorphismDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.ModuleSumSwap,
		module.ModuleSumSmul,
		module.ModuleSumSmulRight,
		module.ModuleSumSupport,
		module.ModuleSumCongruence,
		module.SmulMul,
		function_module.FiniteSuppDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀ι'':(((H → num) → M) → Z). " +
			"∀R'':ring_ops(M). " +
			"∀φ':(B → M). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀V:set(H). " +
			"∀Φ:(E → C). " +
			"∀Φ':(C → Z). " +
			"∀K:ring_ops(F). " +
			"∀ε:(Z → F). " +
			"∀ε':(C → F). " +
			"∀N:module_ops(F, G). " +
			"∀u:(D → G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_embedding(R'', ι'')",
			"comm_ring_on(R'')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"free_algebra_homomorphism(ι', ι'', R', R'', φ', T, V, Φ')",
			"ring_homomorphism(free_algebra_ring(ι'', R'', V), K, ε)",
			"module_on(K, N)",
			"∀y:C. y ∈ free_algebra(ι', R', T) ⇒ ε'(y) = ε(Φ'(y))",
			"u ∈ finite_supp(N.zero, N.carrier, S)",
		},
		Conclusion: "free_algebra_jacobian(ι, ι'', R, R'', S, V, λx:E. Φ'(Φ(x)), ε, N, u) = " +
			"free_algebra_jacobian(ι', " +
			"    ι'', " +
			"    R', " +
			"    R'', " +
			"    T, " +
			"    V, " +
			"    Φ', " +
			"    ε, " +
			"    N, " +
			"    free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε', N, u))",
	},
		"at v ∈ V, ChainRule for Φ' at Φ(var s), a member of the algebra on T, gives ∂_v Φ'(Φ(var s)) = "+
			"Σ_t Φ'(∂_t Φ(var s)) * ∂_v Φ'(var t); ε keeps the finite sum and the products (MapAdd, MapMul), "+
			"and ε ∘ Φ' is ε' on the algebra on T, where ∂_t Φ(var s) lies (PartialIn). So the left side is "+
			"Σ_s Σ_t ε(∂_v Φ'(var t)) ε'(∂_t Φ(var s)) • u(s); exchange the finite sums (ModuleSumSwap, the "+
			"index sets enlarged by ModuleSumSupport) and collect with SmulMul and ModuleSumSmul into Σ_t "+
			"ε(∂_v Φ'(var t)) • J(Φ, ε')(u)(t), the inner value finitely supported on T (JacobianCongruence "+
			"trading ε' for λy. ε(Φ'(y)), a ring map, then JacobianHom). Outside V both sides are N.zero"),
	Reading: "ε' need not be a ring map: it is read only on the algebra on T, where the inner " +
		"Jacobian reads it, so an augmentation that agrees with ε ∘ Φ' only on the algebra — as an " +
		"augmentation of a simplicial algebra agrees with the augmentation one dimension down after " +
		"a face — serves; the composite is the λ-term λx. Φ'(Φ(x)), read only at the variables of S.",
})}

// JacobianBlockTriangular — an algebra map from the algebra on S₁ ∪ S₂
// to the algebra on T₁ ∪ T₂ that sends the variables of S₁ into the
// algebra on T₁ has a block triangular Jacobian: it carries the
// functions on S₁ to functions on T₁, and its block from S₂ to T₂ is the
// map it induces on the quotients, the restriction to S₂ followed by the
// projection to T₂.
var JacobianBlockTriangular = jacobianBlockTriangularThm{family.Add(registry.ProofEntry{
	Name: "JacobianBlockTriangular",
	Key:  "prop_a2c845ac31b3f0db",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianDef,
		JacobianHom,
		PartialIn,
		PartialSupportFinite,
		ring_homomorphism.AdditiveHomomorphism,
		module.ZeroSmul,
		module.ModuleSumSupport,
		module.ModuleSumCongruence,
		function_module.FiniteSuppDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S₁ S₂:set(D). " +
			"∀T₁ T₂:set(I). " +
			"∀Φ:(E → C). " +
			"∀K:ring_ops(F). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S₁ ∪ S₂, T₁ ∪ T₂, Φ)",
			"ring_homomorphism(free_algebra_ring(ι', R', T₁ ∪ T₂), K, ε)",
			"module_on(K, N)",
			"disjoint(T₁, T₂)",
			"∀s:D. s ∈ S₁ ⇒ Φ(free_algebra_var(ι, R, s)) ∈ free_algebra(ι', R', T₁)",
		},
		Conclusion: "(∀u:(D → G). " +
			"    u ∈ finite_supp(N.zero, N.carrier, S₁) ⇒ " +
			"    free_algebra_jacobian(ι, ι', R, R', S₁, T₁ ∪ T₂, Φ, ε, N, u) ∈ " +
			"    finite_supp(N.zero, N.carrier, T₁)) ∧ " +
			"(∀u:(D → G). " +
			"    u ∈ finite_supp(N.zero, N.carrier, S₁ ∪ S₂) ⇒ " +
			"    free_algebra_jacobian(ι, ι', R, R', S₁ ∪ S₂, T₂, Φ, ε, N, u) = " +
			"    free_algebra_jacobian(ι, ι', R, R', S₂, T₂, Φ, ε, N, u))",
	},
		"for s ∈ S₁, Φ(var s) lies in the algebra on T₁, so its derivative in a variable outside T₁ "+
			"is zero (PartialSupportFinite) and the entry is ε of zero, zero (AdditiveHomomorphism, "+
			"ZeroSmul). First part: the image is finitely supported in N's carrier (JacobianHom) and zero "+
			"off T₁. Second part: at t ∈ T₂, outside T₁ by disjointness, the terms at s ∈ S₁ vanish, so "+
			"the sum over the support in S₁ ∪ S₂ is the sum over the support in S₂ (ModuleSumSupport)"),
	Reading: "The second part says that projecting both sides onto T₂ and S₂ commutes with the " +
		"Jacobians: J(S₂, T₂) reads u on S₂ only and writes T₂ only, the map on the quotients. " +
		"Identifying this block with the Jacobian of the map with S₁ and T₁ sent into the coefficients " +
		"is a further step, through PartialBaseChange. Disjointness of T₁ and T₂ is load-bearing for " +
		"the second part: at a variable of both, the derivatives of Φ(var s), s ∈ S₁, would be read.",
})}

// JacobianCongruence — the Jacobian and its transpose read Φ only at the
// variables of S and ε only on the algebra on T: maps that agree there
// have the same Jacobian and the same transpose.
var JacobianCongruence = jacobianCongruenceThm{family.Add(registry.ProofEntry{
	Name: "JacobianCongruence",
	Key:  "prop_b12560fa9a435b02",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianDef,
		FreeAlgebraJacobianTransposeDef,
		PartialIn,
		module.ModuleSumCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ Ψ:(E → C). " +
			"∀ε ε':(C → F). " +
			"∀N:module_ops(F, G).",
		Hypotheses: []string{
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R')",
			"∀s:D. " +
				"    s ∈ S ⇒ " +
				"    Φ(free_algebra_var(ι, R, s)) = Ψ(free_algebra_var(ι, R, s)) ∧ " +
				"    Φ(free_algebra_var(ι, R, s)) ∈ free_algebra(ι', R', T)",
			"∀y:C. y ∈ free_algebra(ι', R', T) ⇒ ε(y) = ε'(y)",
		},
		Conclusion: "free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε, N) = " +
			"free_algebra_jacobian(ι, ι', R, R', S, T, Ψ, ε', N) ∧ " +
			"free_algebra_jacobian_transpose(ι, ι', R, R', S, T, Φ, ε, N) = " +
			"free_algebra_jacobian_transpose(ι, ι', R, R', S, T, Ψ, ε', N)",
	},
		"at a variable s of S both read ε at ∂_t Φ(var s) = ∂_t Ψ(var s), a member of "+
			"the algebra on T (PartialIn), where ε and ε' agree; the index sets agree and "+
			"so do the terms (ModuleSumCongruence), and outside S or T both are N.zero"),
	Reading: "No finiteness or linearity is asked: it holds for every u and w, finite or " +
		"not, because the two sums run over the same index set and their fold step functions " +
		"are extensionally equal. It is the step that replaces a composite of faces by " +
		"another equal to it on the algebra, and an augmentation by one equal to it there.",
})}

// ---------------------------------------------------------------------------
// The transpose
// ---------------------------------------------------------------------------

// JacobianTransposeHom — the transpose of the Jacobian of an algebra map
// is a homomorphism from the functions on T with values in N to the
// functions on S.
var JacobianTransposeHom = jacobianTransposeHomThm{family.Add(registry.ProofEntry{
	Name: "JacobianTransposeHom",
	Key:  "prop_fe435ab7e05b91df",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianTransposeDef,
		PartialIn,
		PartialSupportFinite,
		free_algebra.FreeAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraVarDef,
		function_module.FunModuleOn,
		function_module.FunctionModuleDef,
		function_module.FunModuleDef,
		module_homomorphism.ModuleHomomorphismDef,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.ModuleSumIn,
		module.ModuleSumSupport,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
		module.SmulAddRight,
		module.SmulMul,
		module.ZeroSmul,
		finite_set.FiniteSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀K:ring_ops(F). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"ring_homomorphism(free_algebra_ring(ι', R', T), K, ε)",
			"module_on(K, N)",
		},
		Conclusion: "module_homomorphism(K, " +
			"    function_module(N, T), " +
			"    function_module(N, S), " +
			"    free_algebra_jacobian_transpose(ι, ι', R, R', S, T, Φ, ε, N))",
	},
		"both records are modules over K (FunModuleOn). At s ∈ S every index set lies in the finite "+
			"set of t where ∂_t Φ(var s) is nonzero (PartialSupportFinite at Φ(var s), a member of the "+
			"algebra on T; a zero derivative gives ε of zero, ZeroSmul), so each value is a finite sum "+
			"in N's carrier and is zero off S. Extend each sum to that finite set (ModuleSumSupport); "+
			"then ModuleSumAdd with SmulAddRight, and ModuleSumSmul with SmulMul and K commutative"),
})}

// JacobianTransposeCompose — the transpose of the Jacobian of the
// composite Φ' ∘ Φ at ε is the transpose for Φ at ε' after the transpose
// for Φ' at ε, ε' agreeing with ε ∘ Φ' on the algebra on T.
var JacobianTransposeCompose = jacobianTransposeComposeThm{family.Add(registry.ProofEntry{
	Name: "JacobianTransposeCompose",
	Key:  "prop_e537e681abf7126b",
	Deps: []registry.EntryLike{
		FreeAlgebraJacobianTransposeDef,
		ChainRule,
		JacobianTransposeHom,
		PartialIn,
		PartialSupportFinite,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.AdditiveHomomorphism,
		module.ModuleSumSwap,
		module.ModuleSumSmul,
		module.ModuleSumSmulRight,
		module.ModuleSumSupport,
		module.SmulMul,
		function_module.FunModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀ι'':(((H → num) → M) → Z). " +
			"∀R'':ring_ops(M). " +
			"∀φ':(B → M). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀V:set(H). " +
			"∀Φ:(E → C). " +
			"∀Φ':(C → Z). " +
			"∀K:ring_ops(F). " +
			"∀ε:(Z → F). " +
			"∀ε':(C → F). " +
			"∀N:module_ops(F, G). " +
			"∀w:(H → G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_embedding(R'', ι'')",
			"comm_ring_on(R'')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"free_algebra_homomorphism(ι', ι'', R', R'', φ', T, V, Φ')",
			"ring_homomorphism(free_algebra_ring(ι'', R'', V), K, ε)",
			"module_on(K, N)",
			"∀y:C. y ∈ free_algebra(ι', R', T) ⇒ ε'(y) = ε(Φ'(y))",
			"w ∈ fun_module(N.zero, N.carrier, V)",
		},
		Conclusion: "free_algebra_jacobian_transpose(ι, ι'', R, R'', S, V, λx:E. Φ'(Φ(x)), ε, N, w) = " +
			"free_algebra_jacobian_transpose(ι, " +
			"    ι', " +
			"    R, " +
			"    R', " +
			"    S, " +
			"    T, " +
			"    Φ, " +
			"    ε', " +
			"    N, " +
			"    free_algebra_jacobian_transpose(ι', ι'', R', R'', T, V, Φ', ε, N, w))",
	},
		"at s ∈ S the right side is Σ_t ε'(∂_t Φ(var s)) • Σ_v ε(∂_v Φ'(var t)) • w(v), all sums "+
			"finite (PartialSupportFinite); exchange them (ModuleSumSwap over enlarged index sets, "+
			"ModuleSumSupport), collect the scalars (SmulMul, ModuleSumSmulRight), and ChainRule for Φ' "+
			"at Φ(var s) with ε keeping sums and products (MapAdd, MapMul) and ε' = ε ∘ Φ' on the "+
			"algebra on T turns the scalar at v into ε(∂_v Φ'(Φ(var s))). Outside S both sides are N.zero"),
	Reading: "w is any function on V with values in N's carrier, zero off V; the " +
		"coboundary of a cosimplicial module of such functions reads its identities off " +
		"this one. ε' need not be a ring map: only its values on the algebra on T are read.",
})}

// JacobianTransposeAgreement — precomposing with the Jacobian over the
// scalar ring K is the transpose of the Jacobian with values in N.
var JacobianTransposeAgreement = jacobianTransposeAgreementThm{family.Add(registry.ProofEntry{
	Name: "JacobianTransposeAgreement",
	Key:  "prop_75b9723df5c8670c",
	Reading: "The left side is Hom(−, N) applied to the Jacobian with coefficients in the " +
		"regular module of K, read on the generators of the free module on S; the right side is the " +
		"transpose with values in N. It identifies the coboundary cotangent_cochain is written with " +
		"as the transpose of the cotangent complex's boundary with coefficients in the base ring.",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeDef,
		function_module.FunModuleDef,
		FreeAlgebraJacobianTransposeDef,
		JacobianDelta,
		PartialIn,
		PartialSupportFinite,
		free_algebra.FreeAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraVarIn,
		free_module.FreeLiftDef,
		free_module.DeltaAtDef,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		module.RegularModuleOn,
		module.ModuleSumSupport,
		module.ZeroSmul,
		module.SmulIn,
		comm_ring.MulMonoidOn,
		comm_monoid.RightIdentityOn,
		finite_set.FiniteSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀Φ:(E → C). " +
			"∀K:ring_ops(F). " +
			"∀ε:(C → F). " +
			"∀N:module_ops(F, G). " +
			"∀w:(I → G).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_homomorphism(ι, ι', R, R', φ, S, T, Φ)",
			"ring_homomorphism(free_algebra_ring(ι', R', T), K, ε)",
			"module_on(K, N)",
			"w ∈ fun_module(N.zero, N.carrier, T)",
		},
		Conclusion: "hom_precompose(K, " +
			"    N, " +
			"    S, " +
			"    free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε, regular_module(K)), " +
			"    w) = " +
			"free_algebra_jacobian_transpose(ι, ι', R, R', S, T, Φ, ε, N, w)",
	},
		"off S both sides are N.zero (HomPrecomposeDef, FreeAlgebraJacobianTransposeDef). At s "+
			"∈ S the left side is free_lift of w at the Jacobian, with coefficients in the regular "+
			"module regular_module(K) (a module over the commutative ring K that module_on(K, N) "+
			"carries, RegularModuleOn), of the generator δ_s = delta_at(s), whose value at t is "+
			"ε(∂_t Φ(var s)) * K.one = ε(∂_t Φ(var s)) (JacobianDelta, the entry in K's carrier by "+
			"MapIn, RightIdentityOn), K.zero off T. So it is the sum of ε(∂_t Φ(var s)) • w(t) "+
			"over the t where the scalar is nonzero, a finite set inside T (PartialSupportFinite, "+
			"AdditiveHomomorphism); the right side sums the same terms over the t ∈ T where the "+
			"term is nonzero, a subset of it, and ModuleSumSupport equates them, the other terms "+
			"being K.zero • w(t) = N.zero with w(t) ∈ N.carrier (ZeroSmul)"),
})}
