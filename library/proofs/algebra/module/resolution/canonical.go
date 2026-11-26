// canonical.go — the canonical free resolution of a module over a fixed
// ring. One injection of eventually constant functions is fixed for each
// pair of scalar and carrier types. Every kernel is encoded by that same
// injection; no new choice of a resolution is made in a theorem.

package resolution

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// carrierEmbeddingDef — encode b by all pairs (0, (a, b)).
var carrierEmbeddingDef = carrierEmbeddingDefThm{family.Define(registry.DefEntry{
	Name: "carrierEmbeddingDef", Const: "carrier_embedding", Type: "B → set(prod(num, prod(A, B)))",
	Key: "prop_629ae95570a4db37",
	Equations: []string{
		"∀b:B. carrier_embedding(b) = {x:prod(num, prod(A, B)) | fst(x) = 0 ∧ snd(snd(x)) = b}",
	},
})}

// IndexEmbeddingDef — fix one injection, independent of the ring zero and the degree.
var IndexEmbeddingDef = indexEmbeddingDefThm{family.Define(registry.DefEntry{
	Name:  "IndexEmbeddingDef",
	Const: "index_embedding",
	Type:  "(set(prod(num, prod(A, B))) → A) → set(prod(num, prod(A, B)))",
	Key:   "prop_78cd7d328d39e5c1",
	Equations: []string{
		"index_embedding = " +
			"(εj:((set(prod(num, prod(A, B))) → A) → set(prod(num, prod(A, B)))). " +
			"    injective_on({v:(set(prod(num, prod(A, B))) → A) | eventually_constant(v)}, j))",
	},
})}

// carrierPreimageDef — decode by the inverse of the carrier encoding on
// the carrier; its value off the encoded carrier is unused.
var carrierPreimageDef = carrierPreimageDefThm{family.Define(registry.DefEntry{
	Name:  "carrierPreimageDef",
	Const: "carrier_preimage",
	Type:  "module_ops(A, B) → set(prod(num, prod(A, B))) → B",
	Key:   "prop_3b8b0f4f1b32b4f1",
	Equations: []string{
		"∀M:module_ops(A, B). ∀j:set(prod(num, prod(A, B))). " +
			"    carrier_preimage(M, j) = inverse_on(M.carrier, carrier_embedding⟨A:A, B:B⟩, j)",
	},
	Deps: []registry.EntryLike{carrierEmbeddingDef},
})}

// IndexPreimageDef — decode by the inverse of the fixed encoding on the
// eventually constant functions.
var IndexPreimageDef = indexPreimageDefThm{family.Define(registry.DefEntry{
	Name:  "IndexPreimageDef",
	Const: "index_preimage",
	Type:  "set(prod(num, prod(A, B))) → (set(prod(num, prod(A, B))) → A)",
	Key:   "prop_105fe3156c878d98",
	Equations: []string{
		"∀j:set(prod(num, prod(A, B))). " +
			"    index_preimage(j) = " +
			"    inverse_on({v:(set(prod(num, prod(A, B))) → A) | eventually_constant(v)}, " +
			"        index_embedding⟨A:A, B:B⟩, " +
			"        j)",
	},
	Deps: []registry.EntryLike{IndexEmbeddingDef},
})}

// CanonicalEpsDef — extend the inverse of the carrier embedding linearly.
var CanonicalEpsDef = canonicalEpsDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalEpsDef",
	Const: "canonical_eps",
	Type:  "ring_ops(A) → module_ops(A, B) → (set(prod(num, prod(A, B))) → A) → B",
	Key:   "prop_17a23ecc71df629d",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). " +
			"    canonical_eps(R, M) = free_lift(R.zero, M.add, M.zero, M.smul, carrier_preimage(M))",
	},
	Deps: []registry.EntryLike{carrierPreimageDef},
})}

// CanonicalKernelAtDef — at zero use the augmentation kernel; at positive degrees use the boundary kernel.
var CanonicalKernelAtDef = canonicalKernelAtDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalKernelAtDef",
	Const: "canonical_kernel_at",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"num → " +
		"prod(set(set(prod(num, prod(A, B)))), " +
		"    (set(prod(num, prod(A, B))) → A) → (set(prod(num, prod(A, B))) → A)) → " +
		"set((set(prod(num, prod(A, B))) → A))",
	Key: "prop_5f83489c71a62795",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀n:num. " +
			"∀t:prod(set(set(prod(num, prod(A, B)))), " +
			"        (set(prod(num, prod(A, B))) → A) → (set(prod(num, prod(A, B))) → A)). " +
			"    canonical_kernel_at(R, M, n, t) = " +
			"    {v:(set(prod(num, prod(A, B))) → A) | " +
			"        v ∈ finite_supp(R.zero, R.carrier, fst(t)) ∧ " +
			"        COND(n = 0, " +
			"            canonical_eps(R, M, v) = M.zero, " +
			"            snd(t)(v) = fun_zero⟨D:set(prod(num, prod(A, B)))⟩(R.zero))}",
	},
	Deps: []registry.EntryLike{CanonicalEpsDef},
})}

// CanonicalSyzygyDef — recursively encode the preceding kernel as the next basis.
var CanonicalSyzygyDef = canonicalSyzygyDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalSyzygyDef",
	Const: "canonical_syzygy",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"num → " +
		"prod(set(set(prod(num, prod(A, B)))), " +
		"    (set(prod(num, prod(A, B))) → A) → (set(prod(num, prod(A, B))) → A))",
	Key: "prop_acc4593783fbae76",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). " +
			"    canonical_syzygy(R, M, 0) = " +
			"    (image(carrier_embedding⟨A:A, B:B⟩, M.carrier), " +
			"        λv:(set(prod(num, prod(A, B))) → A). fun_zero⟨D:set(prod(num, prod(A, B)))⟩(R.zero))",
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. " +
			"    canonical_syzygy(R, M, suc(n)) = " +
			"    (image(index_embedding⟨A:A, B:B⟩, canonical_kernel_at(R, M, n, canonical_syzygy(R, M, n))), " +
			"        free_lift(R.zero, " +
			"            fun_add⟨D:set(prod(num, prod(A, B)))⟩(R.add), " +
			"            fun_zero⟨D:set(prod(num, prod(A, B)))⟩(R.zero), " +
			"            fun_smul⟨D:set(prod(num, prod(A, B)))⟩(R.mul), " +
			"            index_preimage⟨A:A, B:B⟩))",
	},
	Deps: []registry.EntryLike{
		CanonicalKernelAtDef,
		carrierEmbeddingDef,
		IndexEmbeddingDef,
		IndexPreimageDef,
	},
})}

// CanonicalResolutionTermsDef — the basis set in each degree.
var CanonicalResolutionTermsDef = canonicalResolutionTermsDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalResolutionTermsDef",
	Const: "canonical_resolution_terms",
	Type:  "ring_ops(A) → module_ops(A, B) → num → set(set(prod(num, prod(A, B))))",
	Key:   "prop_dddf6781649eda5b",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. " +
			"    canonical_resolution_terms(R, M, n) = fst(canonical_syzygy(R, M, n))",
	},
	Deps: []registry.EntryLike{CanonicalSyzygyDef},
})}

// CanonicalBoundaryDef — the degree n boundary; its degree zero value is the zero map.
var CanonicalBoundaryDef = canonicalBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalBoundaryDef",
	Const: "canonical_boundary",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"num → " +
		"(set(prod(num, prod(A, B))) → A) → " +
		"(set(prod(num, prod(A, B))) → A)",
	Key: "prop_260543a8b6a40141",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. " +
			"    canonical_boundary(R, M, n) = snd(canonical_syzygy(R, M, n))",
	},
	Deps: []registry.EntryLike{CanonicalSyzygyDef},
})}

// CanonicalKernelDef — the kernel resolved by the next free term.
var CanonicalKernelDef = canonicalKernelDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalKernelDef",
	Const: "canonical_kernel",
	Type:  "ring_ops(A) → module_ops(A, B) → num → set((set(prod(num, prod(A, B))) → A))",
	Key:   "prop_e267627fe9e44b8f",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. " +
			"    canonical_kernel(R, M, n) = canonical_kernel_at(R, M, n, canonical_syzygy(R, M, n))",
	},
	Deps: []registry.EntryLike{CanonicalKernelAtDef, CanonicalSyzygyDef},
})}

// CarrierEmbeddingInjective — the carrier encoding is one-to-one: the
// code of x holds every tagged pair (0, (a, x)), its tag being 0 and its
// second coordinate x. When y has the same code, those pairs lie in the
// code of y, so their second coordinate x is y; and there is such a pair,
// a type never being empty.
var CarrierEmbeddingInjective = carrierEmbeddingInjectiveThm{family.Add(registry.ProofEntry{
	Name: "CarrierEmbeddingInjective",
	Key:  "prop_df0c9b697eef2b83",
	Build: family.Theorem("injective_on(𝕌⟨A:B⟩, carrier_embedding⟨A:A, B:B⟩)",
		Opening(Unfold(functions.InjectiveOnDef), func(arg *Argument) {
			x := arg.FixAs[B]()
			y := arg.FixAs[B]()
			parts := arg.Conjuncts(
				arg.Assume(),
				"x lies in 𝕌",
				"y lies in 𝕌",
				"x and y have one code")
			sameCode := parts[2]
			ownCode := arg.Have(
				"every tagged pair (0, (a, x)) lies in the code of x",
				"∀a:A. (0, (a, x)) ∈ carrier_embedding⟨A:A, B:B⟩(x)",
				Derive(func(b *Argument) {
					a := b.FixAs[A]()
					zero := b.TermAs[Nat]("0")
					tagged := b.TermAs[Prod[A, B]]("(a, x)")
					// The definition is read at x's type B and at the scalar type
					// A, which no argument carries and Go cannot infer, so both
					// are spelled, in the wrapper's order: B, then A.
					b.Show(
						"the pair has tag 0 and second coordinate x",
						BySets(
							carrierEmbeddingDef.At[B, A](x),
							pairs.Fst.At(zero, tagged),
							pairs.Snd.At(zero, tagged),
							pairs.Snd.At(a, x)))
				}))
			otherCode := arg.Have(
				"the code of y is the code of x, so those pairs lie in the code of y",
				"∀a:A. (0, (a, x)) ∈ carrier_embedding⟨A:A, B:B⟩(y)",
				sameCode.RwRev(),
				By(ownCode))
			arg.Show(
				"a pair (0, (a, x)) in the code of y has second coordinate y, and A has an element a, so x = y",
				BySets(
					otherCode,
					carrierEmbeddingDef.At[B, A](y),
					pairs.Snd.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Prod[A, B]]()),
					pairs.Snd.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
		})),
})}

// IndexEmbeddingInjective — the fixed encoding is one-to-one on the
// eventually constant functions: there are no more of them than indices,
// the subsets of the tagged pairs, so some map is injective on them, and
// the encoding is chosen among such maps.
var IndexEmbeddingInjective = indexEmbeddingInjectiveThm{family.Add(registry.ProofEntry{
	Name: "IndexEmbeddingInjective",
	Key:  "prop_e11b7020941bafa0",
	Build: family.Theorem("injective_on( "+
		"    {v:(set(prod(num, prod(A, B))) → A) | eventually_constant(v)}, index_embedding⟨A:A, B:B⟩)",
		func(a *Argument) {
			eventuallyConstantFunctions := a.TermAs[Set[Fun[Set[Prod[Nat, Prod[A, B]]], A]]](
				"{v:(set(prod(num, prod(A, B))) → A) | eventually_constant(v)}")
			indices := a.TermAs[Set[Set[Prod[Nat, Prod[A, B]]]]]("𝕌")
			a.Have(
				"the eventually constant functions inject into the indices, so some map is injective on them",
				"∃j:((set(prod(num, prod(A, B))) → A) → set(prod(num, prod(A, B)))). "+
					"    injective_on({v:(set(prod(num, prod(A, B))) → A) | eventually_constant(v)}, j)",
				By(cardinal.FiniteSupportIntoPowerSet, cardinal.CardLeDef.At(eventuallyConstantFunctions, indices)))
			a.Show(
				"and the fixed encoding is chosen among the maps injective on them",
				Unfold(IndexEmbeddingDef))
		}),
})}

// CarrierPreimageEmbedding — decoding the code of an element of the
// carrier returns that element: the decoder is the inverse of the carrier
// encoding on the carrier, where the encoding is one-to-one as it is on
// all of B.
var CarrierPreimageEmbedding = carrierPreimageEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "CarrierPreimageEmbedding",
	Key:  "prop_c369e666d78ac51",
	Build: family.Theorem(Statement{
		Binders: "∀M:module_ops(A, B). ∀b:B.",
		Hypotheses: []string{
			"b ∈ M.carrier",
		},
		Conclusion: "carrier_preimage(M, carrier_embedding(b)) = b",
	},
		func(a *Argument, M *Expr[ModuleOps[A, B]], b *Expr[B], inCarrier Fact) {
			oneToOne := a.Have(
				"the carrier encoding is one-to-one on the carrier, as on all of B",
				"injective_on(M.carrier, carrier_embedding⟨A:A, B:B⟩)",
				By(CarrierEmbeddingInjective, functions.InjectiveOnSubset, set_order.SubsetUniv))
			a.Show(
				"the decoder is the inverse of the encoding on the carrier, and it returns b",
				Simp(Fwd(carrierPreimageDef)),
				By(functions.InverseOnLeft, oneToOne, inCarrier))
		}),
})}

// IndexPreimageEmbedding — decoding the code of an eventually constant
// function returns that function: the decoder is the inverse of the fixed
// encoding on the eventually constant functions, where the encoding is
// one-to-one.
var IndexPreimageEmbedding = indexPreimageEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "IndexPreimageEmbedding",
	Key:  "prop_e5ecf57b095143b6",
	Build: family.Theorem(Statement{
		Binders: "∀v:(set(prod(num, prod(A, B))) → A).",
		Hypotheses: []string{
			"eventually_constant(v)",
		},
		Conclusion: "index_preimage(index_embedding(v)) = v",
	},
		func(a *Argument, v *Expr[Fun[Set[Prod[Nat, Prod[A, B]]], A]], eventually Fact) {
			inDomain := a.Have(
				"v is one of the eventually constant functions",
				"v ∈ {w:(set(prod(num, prod(A, B))) → A) | eventually_constant(w)}",
				BySets(eventually))
			a.Show(
				"the decoder is the inverse of the encoding on those functions, and it returns v",
				Simp(Fwd(IndexPreimageDef)),
				By(functions.InverseOnLeft, IndexEmbeddingInjective, inDomain))
		}),
})}

// CanonicalTermsEncodeKernel — the basis of degree n + 1 is the image of
// the degree-n kernel under the fixed encoding: the recursion clause at
// suc(n), with suc(n) written n + 1.
var CanonicalTermsEncodeKernel = canonicalTermsEncodeKernelThm{family.Add(registry.ProofEntry{
	Name: "CanonicalTermsEncodeKernel",
	Key:  "prop_406ea08560e7f0ac",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. "+
		"    canonical_resolution_terms(R, M, n + 1) = image(index_embedding, canonical_kernel(R, M, n))",
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], n *Expr[Nat]) {
			a.Show(
				"with n + 1 read as suc(n), the recursion clause makes the two sides one term",
				Simp(
					Rev(nat_arith.Add1),
					Fwd(CanonicalResolutionTermsDef),
					Fwd(CanonicalSyzygyDef),
					Fwd(pairs.Fst),
					Fwd(CanonicalKernelDef)),
				Basic())
		}),
})}

// CanonicalBoundaryFreeLift — the boundary of degree n + 1 is the linear
// extension of the decoder: the recursion clause at suc(n), with suc(n)
// written n + 1.
var CanonicalBoundaryFreeLift = canonicalBoundaryFreeLiftThm{family.Add(registry.ProofEntry{
	Name: "CanonicalBoundaryFreeLift",
	Key:  "prop_7918cf9f9c1c75f4",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. "+
		"    canonical_boundary(R, M, n + 1) = "+
		"    free_lift(R.zero, "+
		"        fun_add⟨D:set(prod(num, prod(A, B)))⟩(R.add), "+
		"        fun_zero⟨D:set(prod(num, prod(A, B)))⟩(R.zero), "+
		"        fun_smul⟨D:set(prod(num, prod(A, B)))⟩(R.mul), "+
		"        index_preimage)",
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], n *Expr[Nat]) {
			a.Show(
				"with n + 1 read as suc(n), the recursion clause makes the two sides one term",
				Simp(Rev(nat_arith.Add1), Fwd(CanonicalBoundaryDef), Fwd(CanonicalSyzygyDef), Fwd(pairs.Snd)),
				Basic())
		}),
})}

// CanonicalKernelInFree — each kernel lies in its free term: a vector of
// the kernel is by definition a vector of the free module on the basis of
// its degree, under one further condition.
var CanonicalKernelInFree = canonicalKernelInFreeThm{family.Add(registry.ProofEntry{
	Name: "CanonicalKernelInFree",
	Key:  "prop_a86c14bd35bcd1d9",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. "+
		"    canonical_kernel(R, M, n) ⊆ "+
		"    finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n))",
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], n *Expr[Nat]) {
			a.Show(
				"the kernel's comprehension asks membership in the free term and one more condition",
				Unfold(CanonicalKernelDef),
				Unfold(CanonicalKernelAtDef),
				Unfold(CanonicalResolutionTermsDef),
				BySets())
		}),
})}

// IndexPreimageInKernel — the decoder carries each basis index of degree
// n + 1 to a vector of the degree-n kernel: the index is the code of some
// vector v of that kernel, v lies in the free term and so has finite
// support and is eventually constant, and on eventually constant
// functions the decoder inverts the encoding.
var IndexPreimageInKernel = indexPreimageInKernelThm{family.Add(registry.ProofEntry{
	Name: "IndexPreimageInKernel",
	Key:  "prop_ce0e19996eb49a6f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀j:set(prod(num, prod(A, B))).",
		Hypotheses: []string{
			"j ∈ canonical_resolution_terms(R, M, n + 1)",
		},
		Conclusion: "index_preimage(j) ∈ canonical_kernel(R, M, n)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			j *Expr[Set[Prod[Nat, Prod[A, B]]]],
			basisIndex Fact,
		) {
			encoded := a.Have(
				"the basis in degree n + 1 is the image of the degree-n "+
					"kernel under the encoding, so j is the code of a kernel vector",
				"j ∈ image(index_embedding, canonical_kernel(R, M, n))",
				Simp(Rev(CanonicalTermsEncodeKernel)),
				By(basisIndex))
			v, encodes := a.ObtainAs[Fun[Set[Prod[Nat, Prod[A, B]]], A]](
				"call that vector v",
				"∃v:(set(prod(num, prod(A, B))) → A). j = index_embedding(v) ∧ v ∈ canonical_kernel(R, M, n)",
				By(encoded, set_basic.InImage))
			parts := a.Conjuncts(
				encodes,
				"j is the code of v",
				"v lies in the degree-n kernel")
			code, inKernel := parts[0], parts[1]
			inFree := a.Have(
				"v lies in the free module of degree n, as the whole kernel does",
				"v ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n))",
				BySets(inKernel, CanonicalKernelInFree.At(R, M, n)))
			support := a.Have(
				"so v has finite support",
				"finite_support(R.zero, v)",
				BySets(a.Unfolded(inFree, function_module.FiniteSuppDef)))
			zero := a.TermAs[A]("R.zero")
			decodes := a.Have(
				"so v is eventually constant, and the decoder returns it",
				"index_preimage(index_embedding(v)) = v",
				By(
					support,
					function_module.FiniteSupportEventuallyConstant.At(zero, v),
					IndexPreimageEmbedding.At(v)))
			a.Show(
				"the decoding of j is v, a vector of the kernel",
				code.Rw(),
				decodes.Rw(),
				By(inKernel))
		}),
})}

// CanonicalEpsHom — the augmentation is a homomorphism from the free
// module of degree 0 to M: the basis of degree 0 is the set of codes of
// the elements of M, the decoder returns each code to the element it
// encodes, and the augmentation is the linear extension of the decoder.
var CanonicalEpsHom = canonicalEpsHomThm{family.Add(registry.ProofEntry{
	Name: "CanonicalEpsHom",
	Key:  "prop_73e9eb79ea5c82d8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    free_module_record(R, canonical_resolution_terms(R, M, 0)), " +
			"    M, " +
			"    canonical_eps(R, M))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			isModule module.ModuleFact[on.R, on.M],
		) {
			basis := a.Have(
				"the basis of degree 0 is the set of codes of the elements of M",
				"canonical_resolution_terms(R, M, 0) = image(carrier_embedding, M.carrier)",
				Simp(Fwd(CanonicalResolutionTermsDef), Fwd(CanonicalSyzygyDef), Fwd(pairs.Fst)),
				Basic())
			decode := a.Have(
				"the decoder carries the code of each element of M back into M",
				Statement{
					Binders: "∀j:set(prod(num, prod(A, B))).",
					Hypotheses: []string{
						"j ∈ image(carrier_embedding, M.carrier)",
					},
					Conclusion: "carrier_preimage(M, j) ∈ M.carrier",
				},
				Derive(func(c *Argument) {
					c.FixAs[Set[Prod[Nat, Prod[A, B]]]]()
					code := c.Assume()
					b, encodes := c.ObtainAs[B](
						"j is the code of an element b of M",
						"∃b:B. j = carrier_embedding(b) ∧ b ∈ M.carrier",
						By(code, set_basic.InImage))
					c.Show(
						"the decoder returns b, which lies in M",
						By(Normalized, encodes, CarrierPreimageEmbedding.At(M, b)))
				}))
			a.Show(
				"the augmentation is the linear extension of the decoder, "+
					"a map carrying the basis into M, so a homomorphism",
				basis.Rw(),
				Simp(Fwd(CanonicalEpsDef)),
				By(free_module.FreeLiftHom.Read(isModule), decode))
		}),
})}

// CanonicalEpsOnto — the augmentation maps the free module of degree 0
// onto the carrier of M.
var CanonicalEpsOnto = canonicalEpsOntoThm{family.Add(registry.ProofEntry{
	Name: "CanonicalEpsOnto",
	Key:  "prop_5ca978c1e24c112c",
	Deps: []registry.EntryLike{
		CanonicalEpsHom,
		CanonicalEpsDef,
		CanonicalResolutionTermsDef,
		CanonicalSyzygyDef,
		CarrierPreimageEmbedding,
		free_module.DeltaAtIn,
		free_module.FreeLiftDelta,
		module_homomorphism.HomIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "image(canonical_eps(R, M), " +
			"    finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, 0))) = " +
			"M.carrier",
	},
		"Each b in M is the image of the basis vector at its code "+
			"carrier_embedding(b): FreeLiftDelta, and CarrierPreimageEmbedding decoding "+
			"that code to b. HomIn at CanonicalEpsHom supplies the reverse inclusion."),
})}

// CanonicalBoundaryHom — each boundary of positive degree is linear: it
// is the linear extension of the decoder, which carries each basis index
// of degree n + 1 to a vector of the degree-n kernel, and that kernel lies
// in the free module of degree n.
var CanonicalBoundaryHom = canonicalBoundaryHomThm{family.Add(registry.ProofEntry{
	Name: "CanonicalBoundaryHom",
	Key:  "prop_ab31c848e005f706",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    free_module_record(R, canonical_resolution_terms(R, M, n + 1)), " +
			"    free_module_record(R, canonical_resolution_terms(R, M, n)), " +
			"    canonical_boundary(R, M, n + 1))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			isModule module.ModuleFact[on.R, on.M],
		) {
			decode := a.Have(
				"the decoder carries each basis index of degree n + 1 into the free module of degree n",
				Statement{
					Binders: "∀j:set(prod(num, prod(A, B))).",
					Hypotheses: []string{
						"j ∈ canonical_resolution_terms(R, M, n + 1)",
					},
					Conclusion: "index_preimage(j) ∈ " +
						"finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n))",
				},
				Derive(func(b *Argument) {
					j := b.FixAs[Set[Prod[Nat, Prod[A, B]]]]()
					basisIndex := b.Assume()
					inKernel := b.Have(
						"the decoder carries j into the degree-n kernel",
						"index_preimage(j) ∈ canonical_kernel(R, M, n)",
						By(IndexPreimageInKernel.At(R, M, n, j), basisIndex))
					b.Show(
						"and that kernel lies in the free module of degree n",
						BySets(inKernel, CanonicalKernelInFree.At(R, M, n)))
				}))
			freeOn := a.Have(
				"the free module of degree n is a module",
				"module_on(R, free_module_record(R, canonical_resolution_terms(R, M, n)))",
				By(free_module.FreeModuleOn, module.RingOn.Read(isModule)))
			a.Show(
				"the boundary is the linear extension of the decoder, a "+
					"map carrying the basis into a module, so a homomorphism",
				Simp(Fwd(CanonicalBoundaryFreeLift)),
				By(free_module.FreeLiftHom.Read(freeOn), decode))
		}),
})}

// CanonicalKernelSubmodule — each kernel is the kernel of a homomorphism
// out of its free term, so a submodule of it: in degree 0 of the
// augmentation, in degree m + 1 of the boundary.
var CanonicalKernelSubmodule = canonicalKernelSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "CanonicalKernelSubmodule",
	Key:  "prop_a3ed2594d186688c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "submodule(R, " +
			"    free_module_record(R, canonical_resolution_terms(R, M, n)), " +
			"    canonical_kernel(R, M, n))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			isModule module.ModuleFact[on.R, on.M],
		) {
			a.Cases(a.Term("n = 0"))
			a.When(
				"in degree 0 the kernel is the kernel of the augmentation",
				func(b *Argument, isZero Fact) {
					epsKernel := b.Have(
						"the degree-0 kernel is the kernel of ε on the free module of degree 0",
						"canonical_kernel(R, M, 0) = "+
							"group_kernel(M.zero, "+
							"    finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, 0)), "+
							"    canonical_eps(R, M))",
						Unfold(CanonicalKernelDef),
						Unfold(CanonicalKernelAtDef),
						Unfold(group_homomorphism.GroupKernelDef),
						Unfold(CanonicalResolutionTermsDef))
					b.Show(
						"ε is a homomorphism out of the free module of degree 0, and its kernel is a submodule",
						isZero.Rw(),
						epsKernel.Rw(),
						By(module_homomorphism.KernelSubmodule.Read(CanonicalEpsHom.Read(isModule))))
				})
			a.Otherwise(
				"in degree m + 1 the kernel is the kernel of the boundary",
				func(b *Argument, nonzero Fact) {
					m, isSucc := b.ObtainAs[Nat](
						"n is a successor",
						"∃m:num. n = m + 1",
						By(nonzero, nat_arith.NonzeroIsSucc.At(n)))
					positive := b.Have(
						"so m + 1 is not 0",
						"m + 1 ≠ 0",
						isSucc.RwRev(),
						By(nonzero))
					boundaryKernel := b.Have(
						"the degree-(m + 1) kernel is the kernel of the boundary in degree m + 1, m + 1 not being 0",
						"canonical_kernel(R, M, m + 1) = "+
							"group_kernel(fun_zero(R.zero), "+
							"    finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, m + 1)), "+
							"    canonical_boundary(R, M, m + 1))",
						Simp(
							Fwd(CanonicalKernelDef),
							Fwd(CanonicalKernelAtDef),
							Fwd(group_homomorphism.GroupKernelDef),
							Fwd(CanonicalResolutionTermsDef),
							Fwd(CanonicalBoundaryDef)),
						By(positive))
					// A grounded reading is no instance for a law to read at, so
					// the boundary's linearity at m is installed as a fact first.
					boundary := b.Simplified(CanonicalBoundaryHom.Read(isModule).At(m))
					b.Show(
						"that boundary is a homomorphism, and the kernel of a homomorphism is a submodule",
						isSucc.Rw(),
						boundaryKernel.Rw(),
						By(module_homomorphism.KernelSubmodule.Read(boundary)))
				})
		}),
})}

// CanonicalImageIsKernel — the image of each boundary of positive degree
// is the kernel of the degree below.
var CanonicalImageIsKernel = canonicalImageIsKernelThm{family.Add(registry.ProofEntry{
	Name: "CanonicalImageIsKernel",
	Key:  "prop_c85e225b7672ae49",
	Deps: []registry.EntryLike{
		CanonicalKernelSubmodule,
		CanonicalBoundaryHom,
		CanonicalBoundaryFreeLift,
		CanonicalTermsEncodeKernel,
		CanonicalKernelInFree,
		IndexPreimageInKernel,
		IndexPreimageEmbedding,
		free_module.FreeLiftDelta,
		free_module.DeltaAtIn,
		free_module.FreeLiftHom,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportEventuallyConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "image(canonical_boundary(R, M, n + 1), " +
			"    finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n + 1))) = " +
			"canonical_kernel(R, M, n)",
	},
		"The boundary is the free lift of the decoder (CanonicalBoundaryFreeLift), so on the basis "+
			"vector at j it is index_preimage(j), a vector of the kernel (FreeLiftDelta, "+
			"IndexPreimageInKernel); the boundary is linear and the kernel a submodule, so the whole image "+
			"stays in the kernel. A kernel vector v lies in its free term (CanonicalKernelInFree) and so is "+
			"eventually constant; its code is a basis index of degree n + 1 (CanonicalTermsEncodeKernel), "+
			"and IndexPreimageEmbedding makes v the boundary of the basis vector there."),
})}

// CanonicalBoundaryTwice — consecutive boundaries of positive degree
// compose to zero on the free module.
var CanonicalBoundaryTwice = canonicalBoundaryTwiceThm{family.Add(registry.ProofEntry{
	Name: "CanonicalBoundaryTwice",
	Key:  "prop_1ed673a07cdb863",
	Deps: []registry.EntryLike{
		CanonicalImageIsKernel,
		CanonicalKernelDef,
		CanonicalKernelAtDef,
		CanonicalBoundaryDef,
		CanonicalResolutionTermsDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀v:(set(prod(num, prod(A, B))) → A).",
		Hypotheses: []string{
			"module_on(R, M)",
			"v ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M, n + 2))",
		},
		Conclusion: "canonical_boundary(R, M, n + 1, canonical_boundary(R, M, n + 2, v)) = " +
			"fun_zero⟨D:set(prod(num, prod(A, B)))⟩(R.zero)",
	},
		"The first boundary lands in the next kernel, defined "+
			"using the next boundary in every positive degree."),
})}

// CanonicalResolution — the canonical terms, boundaries and augmentation
// form a free resolution of M, with no hypothesis on its size.
var CanonicalResolution = canonicalResolutionThm{family.Add(registry.ProofEntry{
	Name: "CanonicalResolution",
	Key:  "prop_2b77f4bad27fbdbb",
	Deps: []registry.EntryLike{
		FreeResolution,
		FreeComplexOf,
		CanonicalEpsHom,
		CanonicalEpsOnto,
		CanonicalKernelSubmodule,
		CanonicalBoundaryHom,
		CanonicalImageIsKernel,
		CanonicalBoundaryTwice,
		CanonicalKernelDef,
		CanonicalKernelAtDef,
		CanonicalResolutionTermsDef,
		CanonicalBoundaryDef,
		free_module.FreeModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "free_resolution(R, " +
			"    M, " +
			"    canonical_resolution_terms(R, M), " +
			"    canonical_boundary(R, M), " +
			"    canonical_eps(R, M))",
	},
		"The free terms are modules, the boundaries are homomorphisms and square to "+
			"zero. CanonicalImageIsKernel gives exactness, including the augmentation "+
			"kernel at zero; CanonicalEpsOnto supplies the augmentation surjection."),
})}
