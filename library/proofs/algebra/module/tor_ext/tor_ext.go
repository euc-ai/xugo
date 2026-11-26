// tor_ext.go — tensor and Hom complexes of free modules, their
// homology and cohomology, and the long exact sequences. Free tensor
// terms are finitely supported functions; free Hom terms are functions
// on a basis, extended by zero outside it. The resolution-dependent
// constructions support comparison with the canonical Tor and Ext
// definitions. The cochain complexes of chain_complex and their snake
// lemma supply the cohomological layer.

package tor_ext

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Free tensor and Hom read as function modules
// ---------------------------------------------------------------------------

// FiniteSuppTensorIso — the tensor product of the free module on S with M
// is the module of finitely supported M-valued functions on S: a pure
// tensor δ_x ⊗ u goes to the function with value u at x.
var FiniteSuppTensorIso = finiteSuppTensorIsoThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppTensorIso",
	Key:  "prop_263d9d3087199ded",
	Deps: []registry.EntryLike{
		function_module.FiniteSuppModuleDef,
		tensor_product.TensorModuleDef,
		free_module.FreeModuleRecordDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSuppModuleOn,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorSpan,
		tensor_product.TensorModuleOn,
		free_module.FreeModuleOn,
		free_module.FreeModuleExpand,
		free_module.DeltaAtIn,
		module_homomorphism.ModuleIsomorphicDef,
		module.ModuleSumDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(I).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    tensor_module(R, free_module_record(R, S), M), " +
			"    finite_supp_module(M, S))",
	},
		"the bilinear map (f, u) ↦ λx. f(x) • u induces a homomorphism out of the tensor product "+
			"(TensorUniversal), onto the finitely supported functions since g = Σ_x δ_x ⊗ g(x) maps to "+
			"g; the inverse g ↦ Σ_{x ∈ supp g} δ_x ⊗ g(x) is a homomorphism and the two compose to "+
			"identities on pure tensors (TensorUniversalUnique) and on the finitely supported functions"),
})}

// FunModuleHomIso — the homomorphisms from the free module on S into M
// are the M-valued functions on S: a homomorphism is read at the
// generators, a function extended by free_lift.
var FunModuleHomIso = funModuleHomIsoThm{family.Add(registry.ProofEntry{
	Name: "FunModuleHomIso",
	Key:  "prop_c9228d7d52dc0451",
	Deps: []registry.EntryLike{
		function_module.FunctionModuleDef,
		hom_module.HomModuleDef,
		free_module.FreeModuleRecordDef,
		function_module.FunModuleDef,
		function_module.FunModuleOn,
		hom_module.HomSetDef,
		hom_module.HomSetModuleOn,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		free_module.FreeLiftUnique,
		free_module.FreeModuleOn,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(I).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    function_module(M, S), " +
			"    hom_module(R, free_module_record(R, S), M))",
	},
		"g ↦ the extension free_lift(g), read as zero off the free module, is a "+
			"homomorphism of the function module into the Hom module; its inverse reads "+
			"a homomorphism at the generators, h ↦ λx. h(delta_at(x)) on S and M.zero "+
			"off it; the composites are the identity by FreeLiftDelta and FreeLiftUnique"),
})}

// ---------------------------------------------------------------------------
// The tensor complex and Tor
// ---------------------------------------------------------------------------

// TensorBoundaryDef — `tensor_boundary(R, N, d, n, g)`: the boundary
// d(n) ⊗ 1 on an N-valued function g of finite support,
// (d(n) ⊗ 1)(g)(y) = Σ_x d(n)(δ_x)(y) • g(x) over the support of g.
var TensorBoundaryDef = tensorBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "TensorBoundaryDef",
	Const: "tensor_boundary",
	Type:  "ring_ops(A) → module_ops(A, C) → (num → (I → A) → I → A) → num → (I → C) → I → C",
	Key:   "prop_fa44afdfb2b05aa",

	Equations: []string{
		"∀R:ring_ops(A). ∀N:module_ops(A, C). ∀d:(num → (I → A) → I → A). ∀n:num. ∀g:(I → C). ∀y:I. " +
			"    tensor_boundary(R, N, d, n, g, y) = " +
			"    module_sum(N.add, " +
			"        N.zero, " +
			"        fun_support(N.zero, g), " +
			"        λx:I. N.smul(d(n)(delta_at(R.zero, R.one, x))(y), g(x)))",
	},
})}

// FiniteSuppMapDef — `finite_supp_map(R, N, k, h)`: a linear
// map k between free modules on two index types, tensored with 1, on
// an N-valued function h of finite support: y ↦ Σ_x k(δ_x)(y) • h(x).
var FiniteSuppMapDef = finiteSuppMapDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteSuppMapDef",
	Const: "finite_supp_map",
	Type:  "ring_ops(A) → module_ops(A, C) → ((I → A) → E → A) → (I → C) → E → C",
	Key:   "prop_8a6ec9fe6e7cad4b",

	Equations: []string{
		"∀R:ring_ops(A). ∀N:module_ops(A, C). ∀k:((I → A) → E → A). ∀h:(I → C). ∀y:E. " +
			"    finite_supp_map(R, N, k, h, y) = " +
			"    module_sum(N.add, " +
			"        N.zero, " +
			"        fun_support(N.zero, h), " +
			"        λx:I. N.smul(k(delta_at(R.zero, R.one, x))(y), h(x)))",
	},
})}

// TensorBoundaryAsFiniteSuppMap — the boundary d(n) ⊗ 1 of the tensor
// complex is d(n) tensored with N as a map of finitely supported
// functions: the two definitions are the same sum over the support.
var TensorBoundaryAsFiniteSuppMap = tensorBoundaryAsFiniteSuppMapThm{family.Add(registry.ProofEntry{
	Name: "TensorBoundaryAsFiniteSuppMap",
	Key:  "prop_6aa413afda343212",
	Build: family.Theorem("∀R:ring_ops(A). ∀N:module_ops(A, C). ∀d:(num → (I → A) → I → A). ∀n:num. "+
		"    tensor_boundary(R, N, d, n) = finite_supp_map(R, N, d(n))",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			N *Expr[ModuleOps[A, C]],
			d *Arrow2[Nat, Fun[I, A], Fun[I, A]],
			n *Expr[Nat],
		) {
			a.Show(
				"both send g to y ↦ Σ_x d(n)(δ_x)(y) • g(x) over the support of g",
				Simp(Fwd(TensorBoundaryDef), Fwd(FiniteSuppMapDef)),
				Refl())
		}),
})}

// FiniteSuppMapHom — a homomorphism k of the free module on S into the
// free module on T, tensored with N, is a homomorphism of the finitely
// supported N-valued functions on S into those on T. On a function g on
// S it is the sum, over the support of g, of the pure tensors
// k(δ_x) ⊗ g(x); each k(δ_x) lies in the free module on T (HomDeltaIn),
// and tensoring with it is a homomorphism of N into the functions on T,
// so the sum is one (FiniteSuppSumHom).
var FiniteSuppMapHom = finiteSuppMapHomThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppMapHom",
	Key:  "prop_16bd829f0854d28",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:set(I). ∀T:set(E). ∀k:((I → A) → E → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_homomorphism(R, free_module_record(R, S), free_module_record(R, T), k)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    finite_supp_module(N, S), " +
			"    finite_supp_module(N, T), " +
			"    finite_supp_map(R, N, k))",
		Abbrev: Abbrev{
			{Name: "pureTensorSum", Text: "λg:(I → C). " +
				"    module_sum(fun_add⟨D:E⟩(N.add), " +
				"        fun_zero⟨D:E⟩(N.zero), " +
				"        fun_support(N.zero, g), " +
				"        λx:I. λy:E. k(delta_at(x), y) • g(x))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			N *Expr[ModuleOps[A, C]],
			S *Expr[Set[I]],
			T *Expr[Set[E]],
			k *Arrow2[Fun[I, A], E, A],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"N is a module over R",
				"k is a homomorphism of the free modules on S and T")
			moduleN, linear := given[0], given[1]
			zeroR, carrierR := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			ring := module.RingOn.Read(moduleN)
			source := a.TermAs[ModuleOps[A, Fun[I, C]]]("finite_supp_module(N, S)")
			target := a.TermAs[ModuleOps[A, Fun[E, C]]]("finite_supp_module(N, T)")
			targetModule := a.Have(
				"the finitely supported functions on T are a module",
				"module_on(R, finite_supp_module(N, T))",
				By(function_module.FiniteSuppModuleOn.Read(moduleN)))

			// A pure tensor f ⊗ u, y ↦ f(y) • u, of a member f of the free
			// module on T and a vector u of N is linear in u.
			pureTensor := a.Have(
				"tensoring a member f of the free module on T with the "+
					"vectors of N is a homomorphism into the functions on T",
				Statement{
					Binders: "∀f:(E → A).",
					Hypotheses: []string{
						"f ∈ finite_supp(R.zero, R.carrier, T)",
					},
					Conclusion: "module_homomorphism(R, N, finite_supp_module(N, T), λu:C. λy:E. f(y) • u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[E, A]]("f")
					fIn := b.Assume()
					parts := b.Conjuncts(
						b.Have(
							"f has finite support inside T and values in R",
							"finite(fun_support(R.zero, f)) ∧ fun_support(R.zero, f) ⊆ T ∧ (∀y:E. f(y) ∈ R.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(fIn)),
						"the support of f is finite",
						"and lies in T",
						"f takes its values in R")
					into := b.Have(
						"each f ⊗ u is a finitely supported function on T",
						"∀u:C. u ∈ N.carrier ⇒ (λy:E. f(y) • u) ∈ finite_supp(N.zero, N.carrier, T)",
						Derive(func(c *Argument) {
							u := c.FixAs[C]("u")
							uIn := c.Assume()
							values := c.Have(
								"each f(y) • u lies in N",
								"∀y:E. f(y) • u ∈ N.carrier",
								By(parts[2], uIn, module.SmulIn.Read(moduleN)))
							smaller := c.Have(
								"f(y) • u vanishes where f does, R.zero • u being N.zero",
								"fun_support(N.zero, λy:E. f(y) • u) ⊆ fun_support(R.zero, f)",
								BySets(uIn, module.ZeroSmul.Read(moduleN).AsFact().At(u)))
							inside := c.Have(
								"so its support lies in T",
								"fun_support(N.zero, λy:E. f(y) • u) ⊆ T",
								BySets(smaller, parts[1]))
							finite := c.Have(
								"and is finite, a part of the support of f",
								"finite(fun_support(N.zero, λy:E. f(y) • u))",
								By(
									parts[0],
									smaller,
									finite_set.FiniteSubset.At(
										c.TermAs[Set[E]]("fun_support(N.zero, λy:E. f(y) • u)"),
										c.TermAs[Set[E]]("fun_support(R.zero, f)"))))
							c.Show(
								"f ⊗ u has finite support inside T and values in N",
								Simp(Fwd(function_module.FiniteSuppMember)),
								By(finite, inside, values))
						}))
					additive := b.Have(
						"f ⊗ (u + v) is f ⊗ u + f ⊗ v, each f(y) distributing over u + v",
						Statement{
							Binders: "∀u v:C.",
							Hypotheses: []string{
								"u ∈ N.carrier",
								"v ∈ N.carrier",
							},
							Conclusion: "(λy:E. f(y) • (u + v)) = fun_add(N.add, λy:E. f(y) • u, λy:E. f(y) • v)",
						},
						Derive(func(c *Argument) {
							u, v := c.FixAs[C]("u"), c.FixAs[C]("v")
							both := c.Conjuncts(
								c.Assume(),
								"u is a vector of N",
								"so is v")
							add := c.TermAs[Op[C]]("N.add")
							left, right := c.TermAs[Fun[E, C]]("λy:E. f(y) • u"), c.TermAs[Fun[E, C]]("λy:E. f(y) • v")
							c.Do(Funext())
							y := c.FixAs[E]("y")
							c.Show(
								"a scalar distributes over a sum of two vectors",
								By(
									parts[2].At(y),
									both[0],
									both[1],
									function_module.FunAddDef.At(add, left, right, y),
									module.SmulAddLeft.Read(moduleN).AsFact().At(c.TermAs[A]("f(y)"), u, v)))
						}))
					homogeneous := b.Have(
						"f ⊗ (c • u) is c • (f ⊗ u), the scalars commuting",
						Statement{
							Binders: "∀c:A. ∀u:C.",
							Hypotheses: []string{
								"c ∈ R.carrier",
								"u ∈ N.carrier",
							},
							Conclusion: "(λy:E. f(y) • c • u) = fun_smul(N.smul, c, λy:E. f(y) • u)",
						},
						Derive(func(c *Argument) {
							scale, u := c.FixAs[A]("c"), c.FixAs[C]("u")
							assumed := c.Conjuncts(
								c.Assume(),
								"c is a scalar",
								"u is a vector of N")
							smul := c.TermAs[Fun2[A, C, C]]("N.smul")
							tensor := c.TermAs[Fun[E, C]]("λy:E. f(y) • u")
							c.Do(Funext())
							y := c.FixAs[E]("y")
							coefficient := c.TermAs[A]("f(y)")
							c.Show(
								"both are (f(y) * c) • u",
								By(
									parts[2].At(y),
									assumed[0],
									assumed[1],
									function_module.FunSmulDef.At(smul, scale, tensor, y),
									module.SmulMul.Read(moduleN).AsFact().At(coefficient, scale, u),
									module.SmulMul.Read(moduleN).AsFact().At(scale, coefficient, u),
									comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(coefficient, scale)))
						}))
					b.Show(
						"so u ↦ f ⊗ u lands in the functions on T and keeps sums and scalings",
						By(moduleN, targetModule, into, additive, homogeneous, module_homomorphism.ModuleHomomorphismDef))
				}))

			// k carries generators into the free module on T, so each k(δ_x)
			// is such an f, and the coefficients k(δ_x)(y) are scalars.
			generators := a.Have(
				"k carries the generator at a point of S into the free module on T",
				"∀x:I. x ∈ S ⇒ k(delta_at(x)) ∈ finite_supp(R.zero, R.carrier, T)",
				a.ForEach(func(x *Expr[I]) Action {
					return By(free_module.HomDeltaIn.At(R, S, T, k, x), linear)
				}))
			coordinates := a.Have(
				"at a point x of S, u ↦ k(δ_x) ⊗ u is a homomorphism of N into the functions on T",
				Statement{
					Binders: "∀x:I.",
					Hypotheses: []string{
						"x ∈ S",
					},
					Conclusion: "module_homomorphism(R, " +
						"    N, " +
						"    finite_supp_module(N, T), " +
						"    λu:C. λy:E. k(delta_at(x), y) • u)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[I]("x")
					inS := b.Assume()
					b.Show(
						"k(δ_x) lies in the free module on T",
						By(pureTensor.At(b.TermAs[Fun[E, A]]("k(delta_at(x))")), generators.At(x), inS))
				}))
			coefficients := a.Have(
				"so the values k(δ_x)(y), the coefficients of the map, are scalars",
				"∀x:I. ∀y:E. x ∈ S ⇒ k(delta_at(x), y) ∈ R.carrier",
				Derive(func(b *Argument) {
					x := b.FixAs[I]("x")
					b.FixAs[E]("y")
					inS := b.Assume()
					b.Show(
						"a member of the free module on T takes its values in R",
						By(
							function_module.FiniteSuppMember.At(zeroR, carrierR, T, b.TermAs[Fun[E, A]]("k(delta_at(x))")),
							generators.At(x),
							inS))
				}))

			sum := a.Have(
				"so the sum, over the support of g, of the pure tensors k(δ_x) "+
					"⊗ g(x) is a homomorphism of the functions on S into those on T",
				"module_homomorphism(R, finite_supp_module(N, S), finite_supp_module(N, T), «pureTensorSum»)",
				By(
					function_module.FiniteSuppSumHom.At(
						R, N, target, S, a.TermAs[Fun2[I, C, Fun[E, C]]]("λx:I. λu:C. λy:E. k(delta_at(x), y) • u")),
					moduleN,
					targetModule,
					coordinates))
			agree := a.Have(
				"on a function g on S, k ⊗ 1 is that sum",
				Statement{
					Binders: "∀g:(I → C).",
					Hypotheses: []string{
						"g ∈ finite_supp(N.zero, N.carrier, S)",
					},
					Conclusion: "finite_supp_map(R, N, k, g) = " +
						"module_sum(fun_add⟨D:E⟩(N.add), " +
						"    fun_zero⟨D:E⟩(N.zero), " +
						"    fun_support(N.zero, g), " +
						"    λx:I. λy:E. k(delta_at(x), y) • g(x))",
				},
				Derive(func(b *Argument) {
					g := b.FixAs[Fun[I, C]]("g")
					gIn := b.Assume()
					parts := b.Conjuncts(
						b.Have(
							"g has finite support inside S and values in N",
							"finite(fun_support(N.zero, g)) ∧ fun_support(N.zero, g) ⊆ S ∧ (∀x:I. g(x) ∈ N.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(gIn)),
						"the support of g is finite",
						"and lies in S",
						"g takes its values in N")
					support := b.TermAs[Set[I]]("fun_support(N.zero, g)")
					tensors := b.TermAs[Fun2[I, E, C]]("λx:I. λy:E. k(delta_at(x), y) • g(x)")
					values := b.Have(
						"each pure tensor over the support takes its values in N",
						"∀x:I. ∀z:E. x ∈ fun_support(N.zero, g) ⇒ k(delta_at(x), z) • g(x) ∈ N.carrier",
						By(parts[1], coefficients, parts[2], module.SmulIn.Read(moduleN), set_basic.SubsetDef))
					b.Show(
						"at each y both are the sum, over the support, of k(δ_x)(y) • g(x)",
						Funext(),
						b.ForEach(func(y *Expr[E]) Action {
							return By(
								FiniteSuppMapDef.At(R, N, k, g, y),
								function_module.ModuleSumApply.Read(moduleN).At(support, tensors, y),
								values,
								parts[0])
						}))
				}))
			a.Show(
				"k ⊗ 1 agrees with that homomorphism on the functions on S, so it is one",
				By(
					module_homomorphism.HomCongruence.At(
						R,
						source,
						target,
						a.TermAs[Fun[Fun[I, C], Fun[E, C]]]("«pureTensorSum»"),
						a.TermAs[Fun[Fun[I, C], Fun[E, C]]]("finite_supp_map(R, N, k)")),
					sum,
					agree))
		}),
})}

// TorOfResolutionDef — `tor_of_resolution(R, S, d, N, n)`: the
// homology of the tensor complex of the specified free resolution.
var TorOfResolutionDef = torOfResolutionDefThm{family.Define(registry.DefEntry{
	Name:  "TorOfResolutionDef",
	Const: "tor_of_resolution",
	Type: "ring_ops(A) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → I → A) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(I → C))",
	Key: "prop_d7163d631a25ee27",

	Equations: []string{
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀N:module_ops(A, C). ∀n:num. " +
			"    tor_of_resolution(R, S, d, N, n) = homology(tensor_complex(R, S, d, N), n)",
	},
	Deps: []registry.EntryLike{TensorComplexOf},
})}

// TensorComplexOf — the tensor complex of a free resolution S with a
// module N: the function modules finite_supp(N, S(n)) and the boundaries
// d(n) ⊗ 1, `tensor_complex(R, S, d, N)` where a complex's terms and
// boundaries stand.
var TensorComplexOf = tensorComplexOfThm{family.Define(registry.DefEntry{
	Name:  "TensorComplexOf",
	Const: "tensor_complex",
	Type: "ring_ops(A) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → I → A) → " +
		"module_ops(A, C) → " +
		"complex_ops(A, I → C)",
	Key: "prop_ef94d02c5ffba5e3",

	Equations: []string{
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀N:module_ops(A, C). " +
			"    tensor_complex(R, S, d, N) = " +
			"    pack_complex(fun_add⟨D:I⟩(N.add), " +
			"        fun_zero⟨D:I⟩(N.zero), " +
			"        fun_neg⟨D:I⟩(N.neg), " +
			"        fun_smul⟨D:I⟩(N.smul), " +
			"        λn:num. finite_supp(N.zero, N.carrier, S(n)), " +
			"        λn:num. tensor_boundary(R, N, d, n))",
	},
	Deps: []registry.EntryLike{TensorBoundaryDef},
})}

// TensorComplex — the tensor complex of a free complex with N is a chain
// complex. Its n-th term is the module of finitely supported N-valued
// functions on S(n) (FiniteSuppModuleOn), and its boundary d(n + 1) ⊗ 1,
// d(n + 1) tensored with N (TensorBoundaryAsFiniteSuppMap), is a
// homomorphism because d(n + 1) is one between the free modules
// (FiniteSuppMapHom). Two boundaries in a row vanish: d(n + 1) ⊗ 1 is
// linear, so it passes through the sum of the pure tensors
// d(n + 2)(δ_x) ⊗ g(x), and on a pure tensor f ⊗ u it is d(n + 1)(f) ⊗ u,
// which vanishes at f = d(n + 2)(δ_x) because the free complex is one.
var TensorComplex = tensorComplexThm{family.Add(registry.ProofEntry{
	Name: "TensorComplex",
	Key:  "prop_8c73360c4b6250da",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"chain_complex(R, free_complex(R, S, d))",
		},
		Conclusion: "chain_complex(R, tensor_complex(R, S, d, N))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			N *Expr[ModuleOps[A, C]],
			S *Arrow[Nat, Set[I]],
			d *Arrow2[Nat, Fun[I, A], Fun[I, A]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"N is a module over R",
				"the free complex of S and d is a chain complex")
			moduleN, free := given[0], given[1]
			zeroR, carrierR := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			ring := module.RingOn.Read(moduleN)

			// The free complex: its boundaries are homomorphisms of the free
			// modules, so they carry generators into the free module below, and
			// the coefficients d(n + 1)(δ_x)(y) are scalars.
			freeHom := a.Have(
				"each boundary of the free complex is a homomorphism of the free modules on S(n + 1) and S(n)",
				"∀n:num. "+
					"    module_homomorphism(R, "+
					"        free_module_record(R, S(n + 1)), "+
					"        free_module_record(R, S(n)), "+
					"        d(n + 1))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					hom := b.Simplified(
						b.Have(
							"d(n + 1) is a homomorphism of the terms of the free complex in degrees n + 1 and n",
							"module_homomorphism(R, "+
								"    complex_module(free_complex(R, S, d), n + 1), "+
								"    complex_module(free_complex(R, S, d), n), "+
								"    d(n + 1))",
							By(chain_complex.ComplexBoundaryHom.Read(free).At(n))),
						Fwd(chain_complex.ComplexModuleDef))
					b.Show(
						"those terms are the free modules on S(n + 1) and S(n)",
						Simp(Fwd(free_module.FreeModuleRecordDef)),
						By(hom))
				}))
			generators := a.Have(
				"d(n + 1) carries the generator at a point of S(n + 1) into the free module on S(n)",
				"∀n:num. ∀x:I. x ∈ S(n + 1) ⇒ d(n + 1, delta_at(x)) ∈ finite_supp(R.zero, R.carrier, S(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					x := b.FixAs[I]("x")
					inS := b.Assume()
					b.Show(
						"a homomorphism of the free modules carries each generator of its source into its target",
						By(
							free_module.HomDeltaIn.At(
								R, S.Apply(b.TermAs[Nat]("n + 1")), S.Apply(n), b.TermAs[Fun2[Fun[I, A], I, A]]("d(n + 1)"), x),
							freeHom.At(n),
							inS))
				}))
			coefficients := a.Have(
				"so its values, the coefficients of the boundary, are scalars",
				"∀n:num. ∀x y:I. x ∈ S(n + 1) ⇒ d(n + 1, delta_at(x), y) ∈ R.carrier",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					x := b.FixAs[I]("x")
					b.FixAs[I]("y")
					inS := b.Assume()
					b.Show(
						"a member of the free module on S(n) takes its values in R",
						By(
							function_module.FiniteSuppMember.At(
								zeroR, carrierR, S.Apply(n), b.TermAs[Fun[I, A]]("d(n + 1, delta_at(x))")),
							generators.At(n, x),
							inS))
				}))

			// A pure tensor f ⊗ u, y ↦ f(y) • u, of a member of the free module
			// and a vector of N.
			pureTensor := a.Have(
				"a member of the free module on s scaling a vector of N is a finitely supported function on s",
				Statement{
					Binders: "∀s:set(I). ∀f:(I → A). ∀u:C.",
					Hypotheses: []string{
						"f ∈ finite_supp(R.zero, R.carrier, s)",
						"u ∈ N.carrier",
					},
					Conclusion: "(λy:I. f(y) • u) ∈ finite_supp(N.zero, N.carrier, s)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[I]]("s")
					b.FixAs[Fun[I, A]]("f")
					u := b.FixAs[C]("u")
					assumed := b.Conjuncts(
						b.Assume(),
						"f lies in the free module on s",
						"u is a vector of N")
					fIn, uIn := assumed[0], assumed[1]
					parts := b.Conjuncts(
						b.Have(
							"f has finite support inside s and values in R",
							"finite(fun_support(R.zero, f)) ∧ fun_support(R.zero, f) ⊆ s ∧ (∀y:I. f(y) ∈ R.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(fIn)),
						"the support of f is finite",
						"and lies in s",
						"f takes its values in R")
					values := b.Have(
						"each f(y) • u lies in N",
						"∀y:I. f(y) • u ∈ N.carrier",
						By(parts[2], uIn, module.SmulIn.Read(moduleN)))
					smaller := b.Have(
						"f(y) • u vanishes where f does, R.zero • u being N.zero",
						"fun_support(N.zero, λy:I. f(y) • u) ⊆ fun_support(R.zero, f)",
						BySets(uIn, module.ZeroSmul.Read(moduleN).AsFact().At(u)))
					inside := b.Have(
						"so its support lies in s",
						"fun_support(N.zero, λy:I. f(y) • u) ⊆ s",
						BySets(smaller, parts[1]))
					finite := b.Have(
						"and is finite, a part of the support of f",
						"finite(fun_support(N.zero, λy:I. f(y) • u))",
						By(
							parts[0],
							smaller,
							finite_set.FiniteSubset.At(
								b.TermAs[Set[I]]("fun_support(N.zero, λy:I. f(y) • u)"),
								b.TermAs[Set[I]]("fun_support(R.zero, f)"))))
					b.Show(
						"f ⊗ u has finite support inside s and values in N",
						Simp(Fwd(function_module.FiniteSuppMember)),
						By(finite, inside, values))
				}))

			// The boundary of g, a sum over the support of g, may run over any
			// finite part of S(n + 1) outside which g vanishes.
			boundarySum := a.Have(
				"d(n + 1) ⊗ 1 sums over any finite part s of S(n + 1) outside which g vanishes",
				Statement{
					Binders: "∀n:num. ∀g:(I → C). ∀s:set(I). ∀y:I.",
					Hypotheses: []string{
						"finite(s)",
						"s ⊆ S(n + 1)",
						"∀x:I. x ∈ s ⇒ g(x) ∈ N.carrier",
						"∀x:I. x ∉ s ⇒ g(x) = N.zero",
					},
					Conclusion: "tensor_boundary(R, N, d, n + 1, g, y) = " +
						"module_sum(N.add, N.zero, s, λx:I. d(n + 1, delta_at(x), y) • g(x))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					g := b.FixAs[Fun[I, C]]("g")
					s := b.FixAs[Set[I]]("s")
					y := b.FixAs[I]("y")
					parts := b.Conjuncts(
						b.Assume(),
						"s is finite",
						"s lies in S(n + 1)",
						"g lies in N on s",
						"g vanishes off s")
					finite, sInside, gOnS, gOff := parts[0], parts[1], parts[2], parts[3]
					inside := b.Have(
						"the support of g lies in s",
						"fun_support(N.zero, g) ⊆ s",
						BySets(gOff))
					terms := b.Have(
						"each term over s is a scalar times a vector of N, so lies in N",
						"∀x:I. x ∈ s ⇒ d(n + 1, delta_at(x), y) • g(x) ∈ N.carrier",
						By(sInside, coefficients, gOnS, module.SmulIn.Read(moduleN), set_basic.SubsetDef))
					vanish := b.Have(
						"off the support of g each term over s is zero",
						"∀x:I. x ∈ s ∧ x ∉ fun_support(N.zero, g) ⇒ d(n + 1, delta_at(x), y) • g(x) = N.zero",
						Derive(func(c *Argument) {
							x := c.FixAs[I]("x")
							where := c.Conjuncts(
								c.Assume(),
								"x is an index of s",
								"outside the support of g")
							zero := c.Have(
								"g vanishes at x",
								"g(x) = N.zero",
								BySets(where[1]))
							inS := c.Have(
								"x lies in S(n + 1)",
								"x ∈ S(n + 1)",
								BySets(where[0], sInside))
							c.Show(
								"a scalar times N.zero is N.zero",
								By(
									zero,
									inS,
									coefficients.At(n, x, y),
									module.SmulZero.Read(moduleN).AsFact().At(c.TermAs[A]("d(n + 1, delta_at(x), y)"))))
						}))
					b.Show(
						"the sum over the support of g is the sum over s",
						By(
							TensorBoundaryDef.At(R, N, d, b.TermAs[Nat]("n + 1"), g, y),
							module.ModuleSumSupport.Read(moduleN).At(
								s,
								b.TermAs[Set[I]]("fun_support(N.zero, g)"),
								b.TermAs[Fun[I, C]]("λx:I. d(n + 1, delta_at(x), y) • g(x)")),
							finite,
							inside,
							terms,
							vanish))
				}))

			// As a function, the boundary of g is the finite sum of the pure
			// tensors d(n + 1)(δ_x) ⊗ g(x).
			expansion := a.Have(
				"d(n + 1) ⊗ 1 sends g to the sum, over the support of g, of the pure tensors d(n + 1)(δ_x) ⊗ g(x)",
				Statement{
					Binders: "∀n:num. ∀g:(I → C).",
					Hypotheses: []string{
						"g ∈ finite_supp(N.zero, N.carrier, S(n + 1))",
					},
					Conclusion: "tensor_boundary(R, N, d, n + 1, g) = " +
						"module_sum(fun_add⟨D:I⟩(N.add), " +
						"    fun_zero⟨D:I⟩(N.zero), " +
						"    fun_support(N.zero, g), " +
						"    λx:I. λy:I. d(n + 1, delta_at(x), y) • g(x))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					g := b.FixAs[Fun[I, C]]("g")
					gIn := b.Assume()
					n1 := b.TermAs[Nat]("n + 1")
					parts := b.Conjuncts(
						b.Have(
							"g has finite support inside S(n + 1) and values in N",
							"finite(fun_support(N.zero, g)) ∧ fun_support(N.zero, g) ⊆ S(n + 1) ∧ (∀x:I. g(x) ∈ N.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(gIn)),
						"the support of g is finite",
						"and lies in S(n + 1)",
						"g takes its values in N")
					terms := b.Have(
						"each pure tensor over the support takes its values in N",
						"∀x z:I. x ∈ fun_support(N.zero, g) ⇒ d(n + 1, delta_at(x), z) • g(x) ∈ N.carrier",
						By(parts[1], coefficients, parts[2], module.SmulIn.Read(moduleN), set_basic.SubsetDef))
					support := b.TermAs[Set[I]]("fun_support(N.zero, g)")
					tensors := b.TermAs[Fun2[I, I, C]]("λx:I. λy:I. d(n + 1, delta_at(x), y) • g(x)")
					b.Show(
						"at each point both sides are the sum over the support of d(n + 1)(δ_x)(y) • g(x)",
						Funext(),
						b.ForEach(func(y *Expr[I]) Action {
							return By(
								TensorBoundaryDef.At(R, N, d, n1, g, y),
								function_module.ModuleSumApply.Read(moduleN).At(support, tensors, y),
								terms,
								parts[0])
						}))
				}))

			// The boundary is a homomorphism of the function modules.
			boundaryHom := a.Have(
				"d(n + 1) ⊗ 1 is a homomorphism of the functions on S(n + 1) into those on S(n)",
				"∀n:num. "+
					"    module_homomorphism(R, "+
					"        finite_supp_module(N, S(n + 1)), "+
					"        finite_supp_module(N, S(n)), "+
					"        tensor_boundary(R, N, d, n + 1))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"it is d(n + 1) tensored with N, and d(n + 1) is a homomorphism of the free modules",
						Simp(Fwd(TensorBoundaryAsFiniteSuppMap)),
						By(
							FiniteSuppMapHom.At(
								R, N, S.Apply(b.TermAs[Nat]("n + 1")), S.Apply(n), b.TermAs[Fun2[Fun[I, A], I, A]]("d(n + 1)")),
							moduleN,
							freeHom.At(n)))
				}))

			// d(n + 1) on a member f of the free module: f is the sum of the
			// f(x) • δ_x, so d(n + 1)(f)(z) is the sum of the f(x) * d(n + 1)(δ_x)(z).
			evaluation := a.Have(
				"d(n + 1)(f)(z) is the sum, over the support of f, of f(x) * d(n + 1)(δ_x)(z)",
				Statement{
					Binders: "∀n:num. ∀f:(I → A). ∀z:I.",
					Hypotheses: []string{
						"f ∈ finite_supp(R.zero, R.carrier, S(n + 1))",
					},
					Conclusion: "d(n + 1, f, z) = " +
						"module_sum(R.add, R.zero, fun_support(R.zero, f), λx:I. f(x) * d(n + 1, delta_at(x), z))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					f := b.FixAs[Fun[I, A]]("f")
					z := b.FixAs[I]("z")
					fIn := b.Assume()
					n1 := b.TermAs[Nat]("n + 1")
					hom := b.Have(
						"d(n + 1) is a homomorphism of the free modules on S(n + 1) and S(n)",
						"module_homomorphism(R, "+
							"    complex_module(free_complex(R, S, d), n + 1), "+
							"    complex_module(free_complex(R, S, d), n), "+
							"    d(n + 1))",
						By(chain_complex.ComplexBoundaryHom.Read(free).At(n)))
					source := b.Have(
						"its source, the free module on S(n + 1), is a module",
						"module_on(R, complex_module(free_complex(R, S, d), n + 1))",
						By(chain_complex.ComplexModules.Read(free).At(n1)))
					parts := b.Conjuncts(
						b.Have(
							"f has finite support inside S(n + 1) and values in R",
							"finite(fun_support(R.zero, f)) ∧ fun_support(R.zero, f) ⊆ S(n + 1) ∧ (∀x:I. f(x) ∈ R.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(fIn)),
						"the support of f is finite",
						"and lies in S(n + 1)",
						"f takes its values in R")
					support := b.TermAs[Set[I]]("fun_support(R.zero, f)")
					expand := b.Have(
						"f is the sum over its support of the f(x) • δ_x",
						"f = "+
							"module_sum(fun_add⟨D:I⟩(R.add), "+
							"    fun_zero⟨D:I⟩(R.zero), "+
							"    fun_support(R.zero, f), "+
							"    λx:I. fun_smul⟨D:I⟩(R.mul, f(x), delta_at(x)))",
						By(free_module.FreeModuleExpand.Read(ring).At(S.Apply(n1), f), fIn))
					generatorsIn := b.Have(
						"the generators at the support lie in the free module on S(n + 1)",
						"∀x:I. x ∈ fun_support(R.zero, f) ⇒ delta_at(x) ∈ finite_supp(R.zero, R.carrier, S(n + 1))",
						By(parts[1], free_module.DeltaAtIn.Read(ring), set_basic.SubsetDef))
					scaled := b.Have(
						"so do their multiples f(x) • δ_x",
						Statement{
							Binders: "∀x:I.",
							Hypotheses: []string{
								"x ∈ fun_support(R.zero, f)",
							},
							Conclusion: "fun_smul⟨D:I⟩(R.mul, f(x), delta_at(x)) ∈ finite_supp(R.zero, R.carrier, S(n + 1))",
						},
						By(generatorsIn, parts[2], module.SmulIn.Read(source)))
					images := b.Have(
						"d(n + 1) sends f(x) • δ_x to w ↦ f(x) * d(n + 1)(δ_x)(w)",
						Statement{
							Binders: "∀x:I.",
							Hypotheses: []string{
								"x ∈ fun_support(R.zero, f)",
							},
							Conclusion: "d(n + 1, fun_smul⟨D:I⟩(R.mul, f(x), delta_at(x))) = " +
								"λw:I. f(x) * d(n + 1, delta_at(x), w)",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[I]("x")
							inSupport := c.Assume()
							coefficient, generator := c.TermAs[A]("f(x)"), c.TermAs[Fun[I, A]]("delta_at(x)")
							mul, image := c.TermAs[Op[A]]("R.mul"), c.TermAs[Fun[I, A]]("d(n + 1, delta_at(x))")
							c.Show(
								"d(n + 1) commutes with scaling, so at each w both sides are f(x) * d(n + 1)(δ_x)(w)",
								Funext(),
								c.ForEach(func(w *Expr[I]) Action {
									return By(
										inSupport,
										generatorsIn.At(x),
										parts[2].At(x),
										module_homomorphism.HomSmul.Read(hom).AsFact().At(coefficient, generator),
										function_module.FunSmulDef.At(mul, coefficient, image, w))
								}))
						}))
					image := b.Have(
						"so d(n + 1)(f) is the sum of these functions",
						"d(n + 1, f) = "+
							"module_sum(fun_add⟨D:I⟩(R.add), "+
							"    fun_zero⟨D:I⟩(R.zero), "+
							"    fun_support(R.zero, f), "+
							"    λx:I. λw:I. f(x) * d(n + 1, delta_at(x), w))",
						CalcEq(
							Leg(
								b.TermAs[Fun[I, A]](
									"d(n + 1, "+
										"    module_sum(fun_add⟨D:I⟩(R.add), "+
										"        fun_zero⟨D:I⟩(R.zero), "+
										"        fun_support(R.zero, f), "+
										"        λx:I. fun_smul⟨D:I⟩(R.mul, f(x), delta_at(x))))"),
								"f is the sum of the f(x) • δ_x",
								expand.RwRev(),
								Basic()),
							Leg(
								b.TermAs[Fun[I, A]](
									"module_sum(fun_add⟨D:I⟩(R.add), "+
										"    fun_zero⟨D:I⟩(R.zero), "+
										"    fun_support(R.zero, f), "+
										"    λx:I. d(n + 1, fun_smul⟨D:I⟩(R.mul, f(x), delta_at(x))))"),
								"d(n + 1), a homomorphism, carries the finite sum term by term",
								By(
									module_homomorphism.HomSum.Read(hom).At(
										support, b.TermAs[Fun[I, Fun[I, A]]]("λx:I. fun_smul⟨D:I⟩(R.mul, f(x), delta_at(x))")),
									scaled,
									parts[0])),
							FinalLeg(
								"and each term to w ↦ f(x) * d(n + 1)(δ_x)(w)",
								By(module.ModuleSumCongruence, images)),
						))
					// The scalars as a module over themselves, at the ring packed from
					// R's parts: a sum read there states R's own sum and carrier.
					regular := module.RegularModuleOn.Read(ring)
					scalars := b.Have(
						"the coefficients over the support of f are scalars",
						"∀x w:I. x ∈ fun_support(R.zero, f) ⇒ d(n + 1, delta_at(x), w) ∈ R.carrier",
						By(parts[1], coefficients, set_basic.SubsetDef))
					products := b.Have(
						"and so are the products f(x) * d(n + 1)(δ_x)(w)",
						"∀x w:I. x ∈ fun_support(R.zero, f) ⇒ f(x) * d(n + 1, delta_at(x), w) ∈ R.carrier",
						By(scalars, parts[2], comm_ring.MulIn.Read(ring)))
					b.Show(
						"a sum of functions into R evaluates term by term at z",
						By(
							image,
							function_module.ModuleSumApply.Read(regular).At(
								support, b.TermAs[Fun2[I, I, A]]("λx:I. λw:I. f(x) * d(n + 1, delta_at(x), w)"), z),
							products,
							parts[0]))
				}))

			// d(n + 1) ⊗ 1 on a pure tensor.
			pureBoundary := a.Have(
				"d(n + 1) ⊗ 1 sends the pure tensor f ⊗ u to d(n + 1)(f) ⊗ u",
				Statement{
					Binders: "∀n:num. ∀f:(I → A). ∀u:C.",
					Hypotheses: []string{
						"f ∈ finite_supp(R.zero, R.carrier, S(n + 1))",
						"u ∈ N.carrier",
					},
					Conclusion: "tensor_boundary(R, N, d, n + 1, λy:I. f(y) • u) = λz:I. d(n + 1, f, z) • u",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					f := b.FixAs[Fun[I, A]]("f")
					u := b.FixAs[C]("u")
					assumed := b.Conjuncts(
						b.Assume(),
						"f lies in the free module on S(n + 1)",
						"u is a vector of N")
					fIn, uIn := assumed[0], assumed[1]
					parts := b.Conjuncts(
						b.Have(
							"f has finite support inside S(n + 1) and values in R",
							"finite(fun_support(R.zero, f)) ∧ fun_support(R.zero, f) ⊆ S(n + 1) ∧ (∀x:I. f(x) ∈ R.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(fIn)),
						"the support of f is finite",
						"and lies in S(n + 1)",
						"f takes its values in R")
					support := b.TermAs[Set[I]]("fun_support(R.zero, f)")
					values := b.Have(
						"each f(y) • u lies in N",
						"∀y:I. f(y) • u ∈ N.carrier",
						By(parts[2], uIn, module.SmulIn.Read(moduleN)))
					offZero := b.Have(
						"f vanishes off its support",
						"∀y:I. y ∉ fun_support(R.zero, f) ⇒ f(y) = R.zero",
						BySets())
					off := b.Have(
						"and so does f(y) • u",
						"∀y:I. y ∉ fun_support(R.zero, f) ⇒ f(y) • u = N.zero",
						b.ForEach(func(y *Expr[I]) Action {
							return By(offZero.At(y), uIn, module.ZeroSmul.Read(moduleN).AsFact().At(u))
						}))
					scalars := b.Have(
						"the coefficients over the support of f are scalars",
						"∀x z:I. x ∈ fun_support(R.zero, f) ⇒ d(n + 1, delta_at(x), z) ∈ R.carrier",
						By(parts[1], coefficients, set_basic.SubsetDef))
					products := b.Have(
						"and so are the products f(x) * d(n + 1)(δ_x)(z)",
						"∀x z:I. x ∈ fun_support(R.zero, f) ⇒ f(x) * d(n + 1, delta_at(x), z) ∈ R.carrier",
						By(scalars, parts[2], comm_ring.MulIn.Read(ring)))
					b.Do(Funext())
					z := b.FixAs[I]("z")
					regroup := b.Have(
						"each term d(n + 1)(δ_x)(z) • (f(x) • u) is (f(x) * d(n + 1)(δ_x)(z)) • u",
						Statement{
							Binders: "∀x:I.",
							Hypotheses: []string{
								"x ∈ fun_support(R.zero, f)",
							},
							Conclusion: "d(n + 1, delta_at(x), z) • f(x) • u = f(x) * d(n + 1, delta_at(x), z) • u",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[I]("x")
							inSupport := c.Assume()
							coefficient, value := c.TermAs[A]("d(n + 1, delta_at(x), z)"), c.TermAs[A]("f(x)")
							c.Show(
								"both are (d(n + 1)(δ_x)(z) * f(x)) • u, the scalars commuting",
								By(
									inSupport,
									scalars.At(x, z),
									parts[2].At(x),
									uIn,
									module.SmulMul.Read(moduleN).AsFact().At(coefficient, value, u),
									comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(coefficient, value)))
						}))
					b.Show(
						"at z the boundary is d(n + 1)(f)(z) • u",
						CalcEq(
							Leg(
								b.TermAs[C](
									"module_sum(N.add, N.zero, fun_support(R.zero, f), λx:I. d(n + 1, delta_at(x), z) • (f(x) • u))"),
								"d(n + 1) ⊗ 1 sums f ⊗ u over the support of f",
								By(
									boundarySum.At(n, b.TermAs[Fun[I, C]]("λy:I. f(y) • u"), support, z),
									parts[0],
									parts[1],
									values,
									off)),
							Leg(
								b.TermAs[C](
									"module_sum(N.add, N.zero, fun_support(R.zero, f), λx:I. f(x) * d(n + 1, delta_at(x), z) • u)"),
								"regroup each term",
								By(module.ModuleSumCongruence, regroup)),
							FinalLeg(
								"u comes out of the sum, which is d(n + 1)(f)(z)",
								By(
									module.ModuleSumSmulRight.Read(moduleN).AsFact().At(
										support, b.TermAs[Fun[I, A]]("λx:I. f(x) * d(n + 1, delta_at(x), z)"), u),
									products,
									parts[0],
									uIn,
									evaluation.At(n, f, z),
									fIn)),
						))
				}))

			// (c) Two boundaries in a row vanish.
			twice := a.Have(
				"two boundaries in a row vanish: d(n + 1) ⊗ 1 kills each pure "+
					"tensor d(n + 2)(δ_x) ⊗ g(x), as d(n + 1) kills d(n + 2)(δ_x)",
				Statement{
					Binders: "∀n:num. ∀g:(I → C).",
					Hypotheses: []string{
						"g ∈ finite_supp(N.zero, N.carrier, S(n + 2))",
					},
					Conclusion: "tensor_boundary(R, N, d, n + 1, tensor_boundary(R, N, d, n + 2, g)) = " +
						"fun_zero⟨D:I⟩(N.zero)",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					g := b.FixAs[Fun[I, C]]("g")
					gIn := b.Assume()
					n1 := b.TermAs[Nat]("n + 1")
					twoSteps := b.Have(
						"n + 2 is two steps above n",
						"n + 1 + 1 = n + 2",
						ByArith())
					inner := b.Have(
						"d(n + 2) ⊗ 1 sends g to the sum of the pure tensors d(n + 2)(δ_x) ⊗ g(x)",
						"tensor_boundary(R, N, d, n + 2, g) = "+
							"module_sum(fun_add⟨D:I⟩(N.add), "+
							"    fun_zero⟨D:I⟩(N.zero), "+
							"    fun_support(N.zero, g), "+
							"    λx:I. λy:I. d(n + 2, delta_at(x), y) • g(x))",
						By(expansion.At(n1, g), twoSteps, gIn))
					parts := b.Conjuncts(
						b.Have(
							"g has finite support inside S(n + 2) and values in N",
							"finite(fun_support(N.zero, g)) ∧ fun_support(N.zero, g) ⊆ S(n + 2) ∧ (∀x:I. g(x) ∈ N.carrier)",
							Simp(Rev(function_module.FiniteSuppMember)),
							By(gIn)),
						"the support of g is finite",
						"and lies in S(n + 2)",
						"g takes its values in N")
					support := b.TermAs[Set[I]]("fun_support(N.zero, g)")
					upper := b.Have(
						"d(n + 2) carries the generator at a point of S(n + 2) into the free module on S(n + 1)",
						"∀x:I. x ∈ S(n + 2) ⇒ d(n + 2, delta_at(x)) ∈ finite_supp(R.zero, R.carrier, S(n + 1))",
						b.ForEach(func(x *Expr[I]) Action {
							return By(generators.At(n1, x), twoSteps)
						}))
					tensors := b.Have(
						"each pure tensor d(n + 2)(δ_x) ⊗ g(x) is a function on S(n + 1)",
						Statement{
							Binders: "∀x:I.",
							Hypotheses: []string{
								"x ∈ fun_support(N.zero, g)",
							},
							Conclusion: "(λy:I. d(n + 2, delta_at(x), y) • g(x)) ∈ finite_supp(N.zero, N.carrier, S(n + 1))",
						},
						By(upper, parts[1], parts[2], pureTensor, set_basic.SubsetDef))
					vanish := b.Have(
						"and d(n + 1) ⊗ 1 sends it to zero",
						Statement{
							Binders: "∀x:I.",
							Hypotheses: []string{
								"x ∈ fun_support(N.zero, g)",
							},
							Conclusion: "tensor_boundary(R, N, d, n + 1, λy:I. d(n + 2, delta_at(x), y) • g(x)) = " +
								"fun_zero⟨D:I⟩(N.zero)",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[I]("x")
							inSupport := c.Assume()
							inS := c.Have(
								"x lies in S(n + 2)",
								"x ∈ S(n + 2)",
								BySets(inSupport, parts[1]))
							pure := c.Have(
								"d(n + 1) ⊗ 1 sends d(n + 2)(δ_x) ⊗ g(x) to d(n + 1)(d(n + 2)(δ_x)) ⊗ g(x)",
								"tensor_boundary(R, N, d, n + 1, λy:I. d(n + 2, delta_at(x), y) • g(x)) = "+
									"(λz:I. d(n + 1, d(n + 2, delta_at(x)), z) • g(x))",
								By(
									pureBoundary.At(n, c.TermAs[Fun[I, A]]("d(n + 2, delta_at(x))"), c.TermAs[C]("g(x)")),
									upper.At(x),
									inS,
									parts[2]))
							zero := c.Have(
								"d(n + 1) kills d(n + 2)(δ_x), the free complex being a chain complex",
								"d(n + 1, d(n + 2, delta_at(x))) = fun_zero⟨D:I⟩(R.zero)",
								By(
									chain_complex.ComplexBoundaryTwice.Read(free).At(n, c.TermAs[Fun[I, A]]("delta_at(x)")),
									inS,
									free_module.DeltaAtIn.Read(ring)))
							c.Show(
								"so the image is R.zero • g(x) = N.zero at every point",
								pure.Rw(),
								zero.Rw(),
								Funext(),
								c.ForEach(func(w *Expr[I]) Action {
									return By(
										Normalized,
										function_module.FunZeroDef.At(c.TermAs[A]("R.zero"), w),
										function_module.FunZeroDef.At(c.TermAs[C]("N.zero"), w),
										module.ZeroSmul.Read(moduleN).AsFact().At(c.TermAs[C]("g(x)")),
										parts[2])
								}))
						}))
					target := b.Have(
						"the functions on S(n) are a module",
						"module_on(R, finite_supp_module(N, S(n)))",
						By(function_module.FiniteSuppModuleOn.Read(moduleN)))
					hom := b.Have(
						"d(n + 1) ⊗ 1 is a homomorphism of the functions on S(n + 1) into those on S(n)",
						"module_homomorphism(R, "+
							"    finite_supp_module(N, S(n + 1)), "+
							"    finite_supp_module(N, S(n)), "+
							"    tensor_boundary(R, N, d, n + 1))",
						By(boundaryHom.At(n)))
					b.Show(
						"d(n + 1) ⊗ 1 sends the sum to the sum of the images, each zero",
						inner.Rw(),
						CalcEq(
							Leg(
								b.TermAs[Fun[I, C]](
									"module_sum(fun_add⟨D:I⟩(N.add), "+
										"    fun_zero⟨D:I⟩(N.zero), "+
										"    fun_support(N.zero, g), "+
										"    λx:I. tensor_boundary(R, N, d, n + 1, λy:I. d(n + 2, delta_at(x), y) • g(x)))"),
								"d(n + 1) ⊗ 1, a homomorphism, carries the finite sum term by term",
								By(
									module_homomorphism.HomSum.Read(hom).At(
										support, b.TermAs[Fun[I, Fun[I, C]]]("λx:I. λy:I. d(n + 2, delta_at(x), y) • g(x)")),
									tensors,
									parts[0])),
							FinalLeg(
								"a finite sum of zeros is zero",
								By(
									module.ModuleSumZero.Read(target).At(
										support,
										b.TermAs[Fun[I, Fun[I, C]]](
											"λx:I. tensor_boundary(R, N, d, n + 1, λy:I. d(n + 2, delta_at(x), y) • g(x))")),
									vanish,
									parts[0])),
						))
				}))

			// The terms of the tensor complex are the function modules, so the
			// first two clauses are FiniteSuppModuleOn and the homomorphisms above.
			tensor := a.TermAs[chain_complex.ComplexOps[A, Fun[I, C]]]("tensor_complex(R, S, d, N)")
			terms := a.Have(
				"the n-th term of the tensor complex is the module of finitely supported functions on S(n)",
				"∀n:num. complex_module(tensor_complex(R, S, d, N), n) = finite_supp_module(N, S(n))",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(
						chain_complex.ComplexModuleDef.At(tensor, n),
						function_module.FiniteSuppModuleDef.At(N, S.Apply(n)))
				}))
			modules := a.Have(
				"so every term of the tensor complex is a module",
				"∀n:num. module_on(R, complex_module(tensor_complex(R, S, d, N), n))",
				By(terms, function_module.FiniteSuppModuleOn.Read(moduleN)))
			homomorphisms := a.Have(
				"and every boundary a homomorphism into the term below",
				"∀n:num. "+
					"    module_homomorphism(R, "+
					"        complex_module(tensor_complex(R, S, d, N), n + 1), "+
					"        complex_module(tensor_complex(R, S, d, N), n), "+
					"        tensor_boundary(R, N, d, n + 1))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"they are the function modules on S(n + 1) and S(n)",
						By(terms.At(b.TermAs[Nat]("n + 1")), terms.At(n), boundaryHom.At(n)))
				}))
			a.Show(
				"modules, homomorphisms and two boundaries in a row vanishing are the clauses of a chain complex",
				Unfold(chain_complex.ChainComplex),
				By(Normalized, modules, homomorphisms, twice))
		}),
})}

// TorModuleOn — Tor_n(M, N) is a module.
var TorModuleOn = torModuleOnThm{family.Add(registry.ProofEntry{
	Name: "TorModuleOn",
	Key:  "prop_d3c461a2c2045a67",
	Deps: []registry.EntryLike{
		TorModuleDef,
		resolution.CanonicalResolution,
		chain_complex.HomologyModuleDef,
		TorDef,
		TensorComplex,
		chain_complex.HomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_on(R, tor_module(R, M, N, n))",
	},
		"HomologyModuleOn at the tensor complex"),
})}

// TorZero — Tor_0(M, N) is the tensor product M ⊗ N: the degree-0 term
// is finite_supp(N, S(0)), every member a cycle, and g ↦ Σ_x eps(δ_x) ⊗ g(x)
// maps it onto M ⊗ N with the boundaries as kernel.
var TorZero = torZeroThm{family.Add(registry.ProofEntry{
	Name: "TorZero",
	Key:  "prop_34e0f94edf056e70",
	Deps: []registry.EntryLike{
		TorModuleDef,
		resolution.CanonicalResolution,
		tensor_product.TensorModuleDef,
		TorDef,
		TorModuleOn,
		TensorComplex,
		function_module.FiniteSuppDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		tensor_product.TensorModuleOn,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorSpan,
		tensor_product.TensorIn,
		tensor_product.TensorAddLeft,
		tensor_product.TensorAddRight,
		tensor_product.TensorSmulLeft,
		tensor_product.TensorSmulRightFactor,
		resolution.ResolutionModule,
		resolution.ResolutionAugmentationHom,
		resolution.ResolutionAugmentationOnto,
		resolution.ResolutionAugmentationKernel,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.FirstIsomorphism,
		module_homomorphism.ProjectionHom,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		free_module.FreeModuleExpand,
		free_module.FreeLiftDelta,
		group.LeftCosetEqOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphic(R, tor_module(R, M, N, 0), tensor_module(R, M, N))",
	},
		"Φ(g) = Σ_{x ∈ supp g} eps(δ_x) ⊗ g(x) is a homomorphism of finite_supp(N, S(0)) onto "+
			"M ⊗ N (eps is onto, pure tensors span); Φ kills the boundaries since eps(d(1)(δ_x)) "+
			"= M.zero; the bilinear β(u, v) = class of λx. f_u(x) • v, f_u a chosen eps-preimage "+
			"of u, is well defined modulo the boundaries (the kernel of eps) and induces ψ: M ⊗ N "+
			"→ Tor_0 (TensorUniversal) with ψ ∘ Φ the projection, so the kernel of Φ is the "+
			"boundaries; FirstIsomorphism, the cycles at 0 being all of finite_supp(N, S(0))"),
})}

// TorZeroNatural — the identification of Tor₀ with the tensor product
// commutes with the maps a homomorphism of the second variable induces:
// tor_map at degree zero is M ⊗ g read through the isomorphisms.
var TorZeroNatural = torZeroNaturalThm{family.Add(registry.ProofEntry{
	Name: "TorZeroNatural",
	Key:  "prop_21d0a2cb96fdc4ef",
	Reading: "The isomorphisms are Φ(s) = Σ_x eps(δ_x) ⊗ g(x) at a representative g of " +
		"the class s, the same formula for every second variable, so the two of one instance " +
		"are the two of any other; M ⊗ g is not a constant of the corpus, so it enters as any " +
		"homomorphism h with h(u ⊗ v) = u ⊗ g(v) on pure tensors — there is exactly one " +
		"(TensorUniversalUnique). It turns statements about tor_map at degree zero, which the " +
		"Tor long exact sequence speaks, into statements about M ⊗ g, which flatness speaks. " +
		"h is unique only on the carrier of M ⊗ N, which suffices, since Φ(s) lies there.",
	Deps: []registry.EntryLike{
		TorZero,
		TorMapDef,
		TorDef,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorSpan,
		chain_complex.HomologyMapCoset,
		resolution.ResolutionAugmentationHom,
		resolution.ResolutionAugmentationOnto,
		resolution.ResolutionAugmentationKernel,
		module_homomorphism.FirstIsomorphism,
		module_homomorphism.ProjectionHom,
		resolution.CanonicalResolution,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀N':module_ops(A, D). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_homomorphism(R, N, N', g)",
		},
		Conclusion: "∃Φ:(set(set(prod(num, prod(A, B))) → C) → set(prod(B, C) → A)). " +
			"∃Φ':(set(set(prod(num, prod(A, B))) → D) → set(prod(B, D) → A)). " +
			"    module_isomorphism(R, tor_module(R, M, N, 0), tensor_module(R, M, N), Φ) ∧ " +
			"    module_isomorphism(R, tor_module(R, M, N', 0), tensor_module(R, M, N'), Φ') ∧ " +
			"    (∀h:(set(prod(B, C) → A) → set(prod(B, D) → A)). " +
			"        module_homomorphism(R, tensor_module(R, M, N), tensor_module(R, M, N'), h) ∧ " +
			"        (∀u:B. ∀v:C. " +
			"            u ∈ M.carrier ∧ v ∈ N.carrier ⇒ " +
			"            h(tensor(R, M, N, u, v)) = tensor(R, M, N', u, g(v))) ⇒ " +
			"        ∀s:set(set(prod(num, prod(A, B))) → C). " +
			"            s ∈ tor(R, M, N, 0) ⇒ Φ'(tor_map(R, M, N', g, 0, s)) = h(Φ(s)))",
	},
		"build Φ and Φ' as TorZero's argument does — TorZero itself states only that the modules are "+
			"isomorphic —: s ↦ Σ_x eps(δ_x) ⊗ w(x) at a representative w of s, a homomorphism onto M ⊗ N "+
			"whose kernel is the boundaries (ResolutionAugmentationHom, ResolutionAugmentationOnto, "+
			"ResolutionAugmentationKernel, FirstIsomorphism, ProjectionHom), well defined because they "+
			"kill the boundaries; tor_map at degree zero sends the class of w to the class of g ∘ w "+
			"(TorMapDef, HomologyMapCoset), so Φ'(tor_map(g)(s)) = Σ_x eps(δ_x) ⊗ g(w(x)) = h(Σ_x "+
			"eps(δ_x) ⊗ w(x)) by h's values on pure tensors and its additivity"),
})}

// TensorChainMap — a chain map between the free complexes of two
// resolutions, tensored with 1 in the function model, is a chain map of
// the tensor complexes.
var TensorChainMap = tensorChainMapThm{family.Add(registry.ProofEntry{
	Name: "TensorChainMap",
	Key:  "prop_f1aaa2c732a2b5c7",
	Deps: []registry.EntryLike{
		chain_complex.ComplexModules,
		resolution.FreeComplexOf,
		TensorComplexOf,
		chain_complex.ChainMapDef,
		FiniteSuppMapDef,
		FiniteSuppMapHom,
		TensorBoundaryDef,
		TensorBoundaryAsFiniteSuppMap,
		TensorComplex,
		function_module.FiniteSuppModuleOn,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
		module.ModuleSumSwap,
		module.ModuleSumSmulRight,
		free_module.FreeModuleExpand,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module_homomorphism.HomIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀g:(num → (I → A) → E → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"chain_complex(R, free_complex(R, S, d))",
			"chain_complex(R, free_complex(R, T, e))",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)",
		},
		Conclusion: "chain_map(R, " +
			"    tensor_complex(R, S, d, N), " +
			"    tensor_complex(R, T, e, N), " +
			"    λn:num. finite_supp_map(R, N, g(n)))",
	},
		"each finite_supp_map(g(n)) is a homomorphism of finite_supp(N, S(n)) into finite_supp(N, "+
			"T(n)), g(n) being a homomorphism of the free modules (FiniteSuppMapHom); the boundaries are "+
			"finite_supp_map at d(n + 1) and at e(n + 1) (TensorBoundaryAsFiniteSuppMap), and the square (e "+
			"⊗ 1)(g ⊗ 1) = (g ⊗ 1)(d ⊗ 1) expands both sides to Σ_x (e(n+1) ∘ g(n+1))(δ_x)(y) • h(x) = Σ_x "+
			"(g(n) ∘ d(n+1))(δ_x)(y) • h(x) by the chain-map square read through FreeModuleExpand and HomSum"),
})}

// TensorHomotopy — a chain homotopy between chain maps of the free
// complexes, tensored with 1, is a chain homotopy of the tensor
// complexes.
var TensorHomotopy = tensorHomotopyThm{family.Add(registry.ProofEntry{
	Name: "TensorHomotopy",
	Key:  "prop_ac609ad486d1c475",
	Deps: []registry.EntryLike{
		chain_complex.ChainMapDef,
		resolution.FreeComplexOf,
		TensorComplexOf,
		chain_complex.ChainHomotopyDef,
		FiniteSuppMapDef,
		FiniteSuppMapHom,
		TensorBoundaryDef,
		TensorBoundaryAsFiniteSuppMap,
		TensorChainMap,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
		module.ModuleSumSwap,
		module.ModuleSumSmulRight,
		free_module.FreeModuleExpand,
		module_homomorphism.HomSum,
		module_homomorphism.HomDiff,
		module_homomorphism.HomNeg,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀g g' h:(num → (I → A) → E → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"chain_complex(R, free_complex(R, S, d))",
			"chain_complex(R, free_complex(R, T, e))",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g')",
			"chain_homotopy(R, free_complex(R, S, d), free_complex(R, T, e), g, g', h)",
		},
		Conclusion: "chain_homotopy(R, " +
			"    tensor_complex(R, S, d, N), " +
			"    tensor_complex(R, T, e, N), " +
			"    λn:num. finite_supp_map(R, N, g(n)), " +
			"    λn:num. finite_supp_map(R, N, g'(n)), " +
			"    λn:num. finite_supp_map(R, N, h(n)))",
	},
		"each finite_supp_map(h(n)) is a homomorphism into the next term "+
			"(FiniteSuppMapHom), and the boundaries are finite_supp_map at d(n + 1) and at "+
			"e(n + 1) (TensorBoundaryAsFiniteSuppMap); the homotopy identity holds at every "+
			"generator δ_x and extends to finite sums by linearity in h, pointwise in y"),
})}

// TorIndependent — two free resolutions of M give isomorphic Tor: the
// comparison theorem gives chain maps both ways whose composites are
// homotopic to the identity, and homotopic maps agree on homology.
var TorIndependent = torIndependentThm{family.Add(registry.ProofEntry{
	Name: "TorIndependent",
	Key:  "prop_68b70bf278b00e7f",
	Deps: []registry.EntryLike{
		TorOfResolutionDef,
		TorModuleDef,
		resolution.CanonicalResolution,
		TorDef,
		TensorComplex,
		TensorChainMap,
		TensorHomotopy,
		resolution.ResolutionComparison,
		resolution.ResolutionComparisonHomotopy,
		resolution.ResolutionModule,
		chain_complex.HomologyMapHom,
		chain_complex.HomologyMapCoset,
		chain_complex.HomotopicSameHomologyMap,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.HomIdentity,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(resolution.FreeResolution.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    homology_module(tensor_complex(R, S, d, N), n), " +
			"    tor_module(R, M, N, n))",
	}),
		"ResolutionComparison lifts the identity of M to chain maps g: P → P' and g': P' "+
			"→ P; g' ∘ g and the identity both lift the identity, so they are chain "+
			"homotopic (ResolutionComparisonHomotopy); tensoring with N preserves chain maps "+
			"and homotopies (TensorChainMap, TensorHomotopy; the identity's and composites' "+
			"function models are the identity and the composites), so the induced maps on "+
			"Tor are mutually inverse (HomologyMapHom, HomotopicSameHomologyMap)"),
})}

// ---------------------------------------------------------------------------
// The long exact sequence of Tor in the second argument
// ---------------------------------------------------------------------------

// TensorComplexesExact — tensoring the resolution with a short exact
// sequence of modules gives a short exact sequence of complexes: a free
// module tensors exactly, which in the function model is exactness
// pointwise.
var TensorComplexesExact = tensorComplexesExactThm{family.Add(registry.ProofEntry{
	Name: "TensorComplexesExact",
	Key:  "prop_30767426ffb321ad",
	Deps: []registry.EntryLike{
		module_homomorphism.ShortExactModules,
		resolution.CanonicalResolution,
		CanonicalTensorComplexDef,
		chain_complex.ShortExactComplexes,
		chain_complex.ExactComplexesDef,
		chain_complex.ChainMapDef,
		TensorComplex,
		function_module.FiniteSuppDef,
		TensorBoundaryDef,
		module_homomorphism.HomSmul,
		module_homomorphism.HomSum,
		module_homomorphism.HomZero,
		module_homomorphism.ExactAtDef,
		module.ModuleSumSupport,
		set_basic.ExtensionWithin,
		functions.InverseOnIn,
		functions.InverseOnRight,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "short_exact_complexes(R, " +
			"    canonical_tensor_complex(R, M, N'), " +
			"    canonical_tensor_complex(R, M, N), " +
			"    canonical_tensor_complex(R, M, N''), " +
			"    λk:num. λg:(set(prod(num, prod(A, B))) → C). λx:set(prod(num, prod(A, B))). i(g(x)), " +
			"    λk:num. λg:(set(prod(num, prod(A, B))) → D). λx:set(prod(num, prod(A, B))). p(g(x)))",
	}),
		"the three tensor complexes (TensorComplex); i ∘ − and p ∘ − commute with the boundaries "+
			"since i and p are linear and carry finite sums to finite sums (HomSum; the support may "+
			"shrink, ModuleSumSupport); in every degree i ∘ − is one-to-one, its image is the kernel "+
			"of p ∘ −, and p ∘ − is onto, each pointwise in x — the preimage of k is x ↦ COND(k(x) = "+
			"N''.zero, N.zero, inverse_on(N.carrier, p, k(x))). The zero branch keeps finite "+
			"support; at the other points short exactness puts k(x) in image(p, N.carrier), and "+
			"InverseOnIn and InverseOnRight give the value's membership and preimage equation"),
})}

// TorLongExactMiddle — the long exact sequence at Tor_n(M, N).
var TorLongExactMiddle = torLongExactMiddleThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactMiddle",
	Key:  "prop_5c71120c13d5d30b",
	Deps: []registry.EntryLike{
		TorZeroDef,
		TorMapDef,
		TorConnectingDef,
		module_homomorphism.ShortExactModules,
		TorDef,
		TensorComplexesExact,
		chain_complex.LongExactMiddle,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(tor_zero(R, M, N'', n), " +
			"    tor(R, M, N', n), " +
			"    tor(R, M, N, n), " +
			"    tor_map(R, M, N, i, n), " +
			"    tor_map(R, M, N'', p, n))",
	}),
		"LongExactMiddle at the short exact sequence of tensor complexes "+
			"(TensorComplexesExact); tor is its homology by definition"),
})}

// TorLongExactQuotient — the long exact sequence at Tor_{n+1}(M, N”).
var TorLongExactQuotient = torLongExactQuotientThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactQuotient",
	Key:  "prop_766197501751fb67",
	Deps: []registry.EntryLike{
		TorZeroDef,
		TorMapDef,
		TorConnectingDef,
		module_homomorphism.ShortExactModules,
		TorDef,
		TensorComplexesExact,
		chain_complex.LongExactQuotient,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(tor_zero(R, M, N', n), " +
			"    tor(R, M, N, n + 1), " +
			"    tor(R, M, N'', n + 1), " +
			"    tor_map(R, M, N'', p, n + 1), " +
			"    tor_connecting(R, M, N', N, i, p, n))",
	}),
		"LongExactQuotient at the short exact sequence of tensor complexes"),
})}

// TorLongExactSub — the long exact sequence at Tor_n(M, N'): the
// connecting homomorphism Tor_{n+1}(M, N”) → Tor_n(M, N') followed by
// i's map.
var TorLongExactSub = torLongExactSubThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactSub",
	Key:  "prop_54826eb1534e8792",
	Deps: []registry.EntryLike{
		TorZeroDef,
		TorMapDef,
		TorConnectingDef,
		module_homomorphism.ShortExactModules,
		TorDef,
		TensorComplexesExact,
		chain_complex.LongExactSub,
		chain_complex.ConnectingHom,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(tor_zero(R, M, N, n), " +
			"    tor(R, M, N'', n + 1), " +
			"    tor(R, M, N', n), " +
			"    tor_connecting(R, M, N', N, i, p, n), " +
			"    tor_map(R, M, N, i, n))",
	}),
		"LongExactSub at the short exact sequence of tensor complexes"),
})}

// TorLongExactEnd — the sequence ends onto: Tor_0(M, N) → Tor_0(M, N”)
// is onto, every member of the degree-0 term lifting pointwise.
var TorLongExactEnd = torLongExactEndThm{family.Add(registry.ProofEntry{
	Name: "TorLongExactEnd",
	Key:  "prop_e0428de76eae8107",
	Deps: []registry.EntryLike{
		TorZeroDef,
		TorMapDef,
		TorConnectingDef,
		module_homomorphism.ShortExactModules,
		TorDef,
		TensorComplexesExact,
		chain_complex.HomologyMapCoset,
		chain_complex.CyclesDef,
		quotient_group.InLeftCosets,
		set_basic.InImage,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "image(tor_map(R, M, N'', p, 0), tor(R, M, N, 0)) = tor(R, M, N'', 0)",
	}),
		"every class at degree 0 is the class of some k ∈ finite_supp(N'', S(0)), all "+
			"members being cycles; k = p ∘ h for the guarded pointwise preimage h ∈ "+
			"finite_supp(N, S(0)), and the class of h maps to the class of k (HomologyMapCoset)"),
})}

// ---------------------------------------------------------------------------
// The Hom complex and Ext
// ---------------------------------------------------------------------------

// HomCoboundaryDef — `hom_coboundary(R, N, S, d, n, g)`:
// the coboundary − ∘ d(n+1) on an N-valued function g on S(n), read as
// the homomorphism it extends to, at a generator x of S(n+1):
// (g ∘ d(n+1))(δ_x) = Σ_y d(n+1)(δ_x)(y) • g(y); zero off S(n+1), where
// the boundary of a generator is not a member of the free module and
// says nothing.
var HomCoboundaryDef = homCoboundaryDefThm{family.Define(registry.DefEntry{
	Name:  "HomCoboundaryDef",
	Const: "hom_coboundary",
	Type: "ring_ops(A) → " +
		"module_ops(A, C) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → I → A) → " +
		"num → " +
		"(I → C) → " +
		"I → " +
		"C",
	Key: "prop_e86a23f55c11a426",

	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀n:num. " +
			"∀g:(I → C). " +
			"∀x:I. " +
			"    hom_coboundary(R, N, S, d, n, g, x) = " +
			"    COND(x ∈ S(n + 1), " +
			"        module_sum(N.add, " +
			"            N.zero, " +
			"            fun_support(R.zero, d(n + 1)(delta_at(R.zero, R.one, x))), " +
			"            λy:I. N.smul(d(n + 1)(delta_at(R.zero, R.one, x))(y), g(y))), " +
			"        N.zero)",
	},
})}

// HomComplexOf — the Hom complex of a free resolution S into a module
// N: the function modules fun_module(N, S(n)) and the coboundaries
// − ∘ d(n+1), `hom_complex(R, S, d, N)` where a cochain complex's terms and
// coboundaries stand.
var HomComplexOf = homComplexOfThm{family.Define(registry.DefEntry{
	Name:  "HomComplexOf",
	Const: "hom_complex",
	Type: "ring_ops(A) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → I → A) → " +
		"module_ops(A, C) → " +
		"complex_ops(A, I → C)",
	Key: "prop_54425d53cf252918",

	Equations: []string{
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀N:module_ops(A, C). " +
			"    hom_complex(R, S, d, N) = " +
			"    pack_complex(fun_add⟨D:I⟩(N.add), " +
			"        fun_zero⟨D:I⟩(N.zero), " +
			"        fun_neg⟨D:I⟩(N.neg), " +
			"        fun_smul⟨D:I⟩(N.smul), " +
			"        λn:num. fun_module(N.zero, N.carrier, S(n)), " +
			"        λn:num. hom_coboundary(R, N, S, d, n))",
	},
	Deps: []registry.EntryLike{HomCoboundaryDef},
})}

// extOfResolutionDef — `ext_of_resolution(R, S, d, N, n)`: the
// cohomology of the Hom complex of the specified free resolution.
var extOfResolutionDef = extOfResolutionDefThm{family.Define(registry.DefEntry{
	Name:  "extOfResolutionDef",
	Const: "ext_of_resolution",
	Type: "ring_ops(A) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → I → A) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(I → C))",
	Key: "prop_c72be66367b8d84d",

	Equations: []string{
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀N:module_ops(A, C). ∀n:num. " +
			"    ext_of_resolution(R, S, d, N, n) = cohomology(hom_complex(R, S, d, N), n)",
	},
	Deps: []registry.EntryLike{HomComplexOf},
})}

// HomComplexDualAgreement — the dual of a free complex based by the
// identity is its Hom complex.
var HomComplexDualAgreement = homComplexDualAgreementThm{family.Add(registry.ProofEntry{
	Name: "HomComplexDualAgreement",
	Key:  "prop_7809ab96ff2e56ce",
	Reading: "No hypothesis: the records are equal for every d, linear or " +
		"not. Ext, the cohomology of hom_complex at the canonical resolution, " +
		"is this construction, and the dual's laws apply to it as stated.",
	Deps: []registry.EntryLike{
		free_complex_duality.FreeDualComplexDef,
		HomComplexOf,
		free_module.HomPrecomposeDef,
		HomCoboundaryDef,
		free_module.FreeLiftDef,
		resolution.FreeComplexOf,
		chain_complex.ComplexDifferentialDef,
		chain_complex.ComplexOpsData.Ext,
	},
	Build: family.Card(
		"∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). "+
			"    free_dual_complex(R, "+
			"        N, "+
			"        free_complex(R, S, d), "+
			"        S, "+
			"        (λn:num. λa:(I → A). a), "+
			"        (λn:num. λa:(I → A). a)) = "+
			"    hom_complex(R, S, d, N)",
		"The two records agree field by field (the complex record's extensionality, ComplexOpsEq): "+
			"the same pointwise operations and the terms fun_module(N.zero, N.carrier, S(n)) "+
			"(FreeDualComplexDef, HomComplexOf); the coboundary out of n is hom_precompose at "+
			"free_complex(R, S, d).d(n + 1) = d(n + 1) (FreeComplexOf, ComplexDifferentialDef), and at "+
			"x ∈ S(n + 1) that is free_lift of g at d(n + 1)(δ_x), the sum over fun_support(R.zero, "+
			"d(n + 1)(δ_x)) of d(n + 1)(δ_x)(y) • g(y) — hom_coboundary's sum term for term "+
			"(HomPrecomposeDef, FreeLiftDef, HomCoboundaryDef) — and N.zero off S(n + 1) on both sides."),
})}

// HomComplex — the Hom complex of a free complex into N is a cochain
// complex. The free complex is based by the identity on its generators,
// the dual of a based complex is a cochain complex, and at that basis the
// dual is the Hom complex.
var HomComplex = homComplexThm{family.Add(registry.ProofEntry{
	Name: "HomComplex",
	Key:  "prop_fb7ccdab67958017",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, C). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"chain_complex(R, free_complex(R, S, d))",
		},
		Conclusion: "cochain_complex(R, hom_complex(R, S, d, N))",
	},
		func(a *Argument, R, N, S, d Term, assumptions Fact) {
			parts := a.Conjuncts(
				assumptions,
				"N is a module",
				"the free complex is a chain complex")
			moduleN, chain := parts[0], parts[1]
			based := a.Have(
				"the free complex is based by the identity on S",
				"based_chain_complex(R, "+
					"    free_complex(R, S, d), "+
					"    S, "+
					"    (λn:num. λa:(I → A). a), "+
					"    (λn:num. λa:(I → A). a))",
				By(chain, free_complex_duality.FreeComplexBased))
			dual := a.Have(
				"its dual with coefficients in N is a cochain complex",
				"cochain_complex(R, "+
					"    free_dual_complex(R, "+
					"        N, "+
					"        free_complex(R, S, d), "+
					"        S, "+
					"        (λn:num. λa:(I → A). a), "+
					"        (λn:num. λa:(I → A). a)))",
				By(moduleN, free_complex_duality.FreeDualCochainComplex.Read(based)))
			a.Show(
				"the Hom complex is that dual, so a cochain complex",
				Simp(Rev(HomComplexDualAgreement)),
				By(dual))
		}),
})}

// ExtModuleOn — Ext^n(M, N) is a module.
var ExtModuleOn = extModuleOnThm{family.Add(registry.ProofEntry{
	Name: "ExtModuleOn",
	Key:  "prop_704159cc98a941f0",
	Deps: []registry.EntryLike{
		ExtModuleDef,
		resolution.CanonicalResolution,
		chain_complex.CohomologyModuleDef,
		ExtDef,
		HomComplex,
		chain_complex.CohomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_on(R, ext_module(R, M, N, n))",
	},
		"CohomologyModuleOn at the Hom complex"),
})}

// ExtZero — Ext^0(M, N) is Hom(M, N): a function on S(0) killed by the
// coboundary extends to a homomorphism free(S(0)) → N vanishing on the
// boundaries, hence factors through the augmentation onto M.
var ExtZero = extZeroThm{family.Add(registry.ProofEntry{
	Name: "ExtZero",
	Key:  "prop_bbb0804cafeb0baf",
	Deps: []registry.EntryLike{
		ExtModuleDef,
		resolution.CanonicalResolution,
		hom_module.HomModuleDef,
		ExtDef,
		HomComplex,
		chain_complex.CocyclesDef,
		chain_complex.CoboundariesDef,
		hom_module.HomSetDef,
		hom_module.HomSetModuleOn,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		free_module.FreeLiftUnique,
		resolution.ResolutionModule,
		resolution.ResolutionAugmentationHom,
		resolution.ResolutionAugmentationOnto,
		resolution.ResolutionAugmentationKernel,
		module_homomorphism.ModuleIsomorphicDef,
		module_homomorphism.HomSum,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphic(R, ext_module(R, M, N, 0), hom_module(R, M, N))",
	},
		"the coboundaries at 0 are {zero}, so Ext^0 is the cocycles; a cocycle g has "+
			"free_lift(g) killing the boundaries, the kernel of eps, so it induces a homomorphism "+
			"M → N through eps (onto), read as zero off M; conversely a homomorphism h: M → N "+
			"gives the cocycle x ↦ h(eps(δ_x)) on S(0), zero off it; the two are inverse and linear"),
})}

// HomCochainMap — a chain map g of free complexes transposes to a cochain
// map of their Hom complexes, in the opposite direction, precomposition
// with g(n) in degree n. Both free complexes are based by the identity on
// their generators; the transpose of a chain map of based complexes is a
// cochain map of the duals, at identity bases that transpose is
// precomposition with g, and the duals are the Hom complexes.
var HomCochainMap = homCochainMapThm{family.Add(registry.ProofEntry{
	Name: "HomCochainMap",
	Key:  "prop_60d30e5968f9705a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀g:(num → (I → A) → E → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"chain_complex(R, free_complex(R, S, d))",
			"chain_complex(R, free_complex(R, T, e))",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)",
		},
		Conclusion: "cochain_map(R, " +
			"    hom_complex(R, T, e, N), " +
			"    hom_complex(R, S, d, N), " +
			"    λn:num. hom_precompose(R, N, S(n), g(n)))",
	},
		func(a *Argument, R, N, S, d, T, e, g Term, assumptions Fact) {
			parts := a.Conjuncts(
				assumptions,
				"N is a module",
				"the free complex on S is a chain complex",
				"the free complex on T is a chain complex",
				"g is a chain map from the first to the second")
			moduleN, chainS, chainT, chainMap := parts[0], parts[1], parts[2], parts[3]
			basedS := a.Have(
				"the free complex on S is based by the identity on its generators",
				"based_chain_complex(R, "+
					"    free_complex(R, S, d), "+
					"    S, "+
					"    (λn:num. λa:(I → A). a), "+
					"    (λn:num. λa:(I → A). a))",
				By(chainS, free_complex_duality.FreeComplexBased))
			basedT := a.Have(
				"and so is the free complex on T",
				"based_chain_complex(R, "+
					"    free_complex(R, T, e), "+
					"    T, "+
					"    (λn:num. λa:(E → A). a), "+
					"    (λn:num. λa:(E → A). a))",
				By(chainT, free_complex_duality.FreeComplexBased))
			transpose := a.Have(
				"at bases given by the identity, transposing g is precomposing with g(n) in each degree n",
				"free_dual_map(R, N, S, (λn:num. λa:(I → A). a), (λn:num. λa:(E → A). a), g) = "+
					"(λn:num. hom_precompose(R, N, S(n), g(n)))",
				Unfold(free_complex_duality.FreeDualMapDef))
			// The transpose law at the basis on S, its target the complex on T
			// with the identity basis, its chain map g.
			complexT, identityT := a.Term("free_complex(R, T, e)"), a.Term("λn:num. λa:(E → A). a")
			transposeLaw := free_complex_duality.FreeDualCochainMap.Read(basedS).AsFact().At(
				N, complexT, T, identityT, identityT, g)
			dual := a.Have(
				"so precomposition with g is a cochain map from the dual on T to the dual on S",
				"cochain_map(R, "+
					"    free_dual_complex(R, "+
					"        N, "+
					"        free_complex(R, T, e), "+
					"        T, "+
					"        (λn:num. λa:(E → A). a), "+
					"        (λn:num. λa:(E → A). a)), "+
					"    free_dual_complex(R, "+
					"        N, "+
					"        free_complex(R, S, d), "+
					"        S, "+
					"        (λn:num. λa:(I → A). a), "+
					"        (λn:num. λa:(I → A). a)), "+
					"    (λn:num. hom_precompose(R, N, S(n), g(n))))",
				transpose.RwRev(),
				By(moduleN, basedT, chainMap, transposeLaw))
			a.Show(
				"the two duals are the two Hom complexes",
				Simp(Rev(HomComplexDualAgreement)),
				By(dual))
		}),
})}

// ExtIndependent — any free resolution P of M computes Ext: the lifts of the
// identity of M between P and the canonical resolution P₀ are inverse chain
// homotopy equivalences, their transposes are a cochain homotopy equivalence
// between the two Hom complexes, and that is an isomorphism on cohomology.
var ExtIndependent = extIndependentThm{family.Add(registry.ProofEntry{
	Name: "ExtIndependent",
	Key:  "prop_ff28e0da927820d8",
	Build: resolution.FreeResolution.Law(Statement{
		Binders: "∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, N)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    cohomology_module(hom_complex(R, S, d, N), n), " +
			"    ext_module(R, M, N, n))",
		Abbrev: Abbrev{
			{Name: "canonicalComplex", Text: "free_complex(R, " +
				"    canonical_resolution_terms(R, M), " +
				"    canonical_boundary(R, M))"},
			{Name: "resolutionDual", Text: "free_dual_complex(R, " +
				"    N, " +
				"    free_complex(R, S, d), " +
				"    S, " +
				"    λn:num. λa:(I → A). a, " +
				"    λn:num. λa:(I → A). a)"},
			{Name: "transposeGʹ", Text: "free_dual_map(R, " +
				"    N, " +
				"    canonical_resolution_terms(R, M), " +
				"    λn:num. λa:(set(prod(num, prod(A, B))) → A). a, " +
				"    λn:num. λa:(I → A). a, " +
				"    g')"},
			{Name: "canonicalDual", Text: "free_dual_complex(R, " +
				"    N, " +
				"    free_complex(R, canonical_resolution_terms(R, M), canonical_boundary(R, M)), " +
				"    canonical_resolution_terms(R, M), " +
				"    λn:num. λa:(set(prod(num, prod(A, B))) → A). a, " +
				"    λn:num. λa:(set(prod(num, prod(A, B))) → A). a)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			S *Arrow[Nat, Set[I]],
			d *Arrow2[Nat, Fun[I, A], Fun[I, A]],
			eps *Arrow[Fun[I, A], B],
			res resolution.FreeResolutionFact[on.R, on.M],
			N *Expr[ModuleOps[A, C]],
			n *Expr[Nat],
			moduleN Fact,
		) {
			// The free complex P₀ of M's canonical resolution, the duals with
			// coefficients in N of P and P₀, each based by the identity on its
			// generators, and the transpose of a chain map g': P₀ → P.
			terms := a.TermAs[Fun2[Nat, Set[Prod[Nat, Prod[A, B]]], Bool]]("canonical_resolution_terms(R, M)")
			boundary := a.TermAs[Fun3[Nat, Fun[Set[Prod[Nat, Prod[A, B]]], A], Set[Prod[Nat, Prod[A, B]]], A]](
				"canonical_boundary(R, M)")
			augmentation := a.TermAs[Fun[Fun[Set[Prod[Nat, Prod[A, B]]], A], B]]("canonical_eps(R, M)")
			identityM := a.TermAs[Fun[B, B]]("identity_map")

			moduleM := resolution.ResolutionModule.Read(res)
			canonical := a.Have(
				"M's canonical resolution is a free resolution",
				"free_resolution(R, "+
					"    M, "+
					"    canonical_resolution_terms(R, M), "+
					"    canonical_boundary(R, M), "+
					"    canonical_eps(R, M))",
				By(resolution.CanonicalResolution, moduleM))
			identity := a.Have(
				"the identity of M is linear",
				"module_homomorphism(R, M, M, identity_map)",
				By(module_homomorphism.HomIdentity, moduleM))

			// The comparison theorem, both ways, at the identity of M.
			_, forth := a.Obtain(
				"the identity of M lifts to a chain map g: P → P₀",
				"∃g:(num → (I → A) → set(prod(num, prod(A, B))) → A). "+
					"    chain_map(R, free_complex(R, S, d), «canonicalComplex», g) ∧ "+
					"    (∀x:(I → A). "+
					"        x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ canonical_eps(R, M)(g(0)(x)) = eps(x))",
				By(
					resolution.ResolutionComparison.Read(res).At(M, terms, boundary, augmentation, identityM),
					canonical,
					identity,
					functions.IdentityApply))
			_, back := a.Obtain(
				"and to a chain map g': P₀ → P",
				"∃g':(num → (set(prod(num, prod(A, B))) → A) → I → A). "+
					"    chain_map(R, «canonicalComplex», free_complex(R, S, d), g') ∧ "+
					"    (∀x:(set(prod(num, prod(A, B))) → A). "+
					"        x ∈ finite_supp(R.zero, R.carrier, canonical_resolution_terms(R, M)(0)) ⇒ "+
					"        eps(g'(0)(x)) = canonical_eps(R, M)(x))",
				By(
					resolution.ResolutionComparison.Read(canonical).At(M, S, d, eps, identityM),
					res,
					identity,
					functions.IdentityApply))
			equivalence := a.Have(
				"the lifts of the identity of M either way are inverse chain homotopy equivalences",
				"chain_homotopy_equivalence(R, «canonicalComplex», free_complex(R, S, d), g', g)",
				By(resolution.ResolutionComparisonEquivalence.Read(canonical), res, back, forth))

			// Transposed with coefficients in N, on the identity bases.
			basedP := a.Have(
				"P is based by the identity on its generators",
				"based_chain_complex(R, free_complex(R, S, d), S, λn:num. λa:(I → A). a, λn:num. λa:(I → A). a)",
				By(free_complex_duality.FreeComplexBased, resolution.ResolutionComplex.Read(res)))
			basedP0 := a.Have(
				"and so is P₀",
				"based_chain_complex(R, "+
					"    «canonicalComplex», "+
					"    canonical_resolution_terms(R, M), "+
					"    λn:num. λa:(set(prod(num, prod(A, B))) → A). a, "+
					"    λn:num. λa:(set(prod(num, prod(A, B))) → A). a)",
				By(free_complex_duality.FreeComplexBased, resolution.ResolutionComplex.Read(canonical)))
			dualEquivalence := a.Have(
				"the transposes of g' and g are a cochain homotopy "+
					"equivalence from the dual of P to the dual of P₀",
				"cochain_homotopy_equivalence(R, "+
					"    «resolutionDual», "+
					"    «canonicalDual», "+
					"    «transposeGʹ», "+
					"    free_dual_map(R, "+
					"        N, "+
					"        S, "+
					"        λn:num. λa:(I → A). a, "+
					"        λn:num. λa:(set(prod(num, prod(A, B))) → A). a, "+
					"        g))",
				By(free_complex_duality.FreeDualHomotopyEquivalence, basedP0, moduleN, basedP, equivalence))
			cochainP := a.Have(
				"the dual of P is a cochain complex",
				"cochain_complex(R, «resolutionDual»)",
				By(moduleN, free_complex_duality.FreeDualCochainComplex.Read(basedP)))
			cochainP0 := a.Have(
				"and so is the dual of P₀",
				"cochain_complex(R, «canonicalDual»)",
				By(moduleN, free_complex_duality.FreeDualCochainComplex.Read(basedP0)))
			isomorphism := a.Have(
				"a cochain homotopy equivalence induces an isomorphism on cohomology",
				"module_isomorphism(R, "+
					"    cohomology_module(«resolutionDual», n), "+
					"    cohomology_module(«canonicalDual», n), "+
					"    cohomology_map(«canonicalDual», «transposeGʹ», n))",
				By(chain_complex.CochainHomotopyEquivalenceIsomorphism.Read(cochainP), cochainP0, dualEquivalence))
			a.Show(
				"the dual of P is the Hom complex of S, and that of "+
					"P₀ the canonical Hom complex, whose cohomology is Ext",
				Simp(
					Fwd(ExtModuleDef),
					Fwd(CanonicalHomComplexDef),
					Rev(HomComplexDualAgreement),
					Fwd(module_homomorphism.ModuleIsomorphicDef)),
				By(isomorphism))
		}),
})}

// HomComplexesExact — mapping the resolution into a short exact
// sequence of modules gives a short exact sequence of Hom complexes:
// the function modules are exact in the module, pointwise.
var HomComplexesExact = homComplexesExactThm{family.Add(registry.ProofEntry{
	Name: "HomComplexesExact",
	Key:  "prop_3808df4b2ac87d8a",
	Deps: []registry.EntryLike{
		free_complex_duality.FreeDualCoefficientShortExact,
		free_complex_duality.FreeComplexBased,
		HomComplexDualAgreement,
		CanonicalHomComplexDef,
		resolution.CanonicalResolution,
		resolution.ResolutionComplex,
		module_homomorphism.ShortExactModules,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "short_exact_cochain_complexes(R, " +
			"    canonical_hom_complex(R, M, N'), " +
			"    canonical_hom_complex(R, M, N), " +
			"    canonical_hom_complex(R, M, N''), " +
			"    λk:num. λg:(set(prod(num, prod(A, B))) → C). λx:set(prod(num, prod(A, B))). i(g(x)), " +
			"    λk:num. λg:(set(prod(num, prod(A, B))) → D). λx:set(prod(num, prod(A, B))). p(g(x)))",
	}),
		"FreeDualCoefficientShortExact at the free complex of M's canonical "+
			"resolution, a chain complex (CanonicalResolution, ResolutionComplex) based "+
			"by the identity (FreeComplexBased); its three duals are the canonical Hom "+
			"complexes of N', N and N'' (HomComplexDualAgreement, CanonicalHomComplexDef)"),
})}

// ExtLongExactStart — the sequence starts one-to-one: Ext^0(M, N') →
// Ext^0(M, N) is one-to-one, i being one-to-one pointwise.
var ExtLongExactStart = extLongExactStartThm{family.Add(registry.ProofEntry{
	Name: "ExtLongExactStart",
	Key:  "prop_888797412553fdb7",
	Deps: []registry.EntryLike{
		ExtMapDef,
		module_homomorphism.ShortExactModules,
		ExtAsCohomology,
		HomComplexesExact,
		chain_complex.CoLongExactStart,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "injective_on(ext(R, M, N', 0), ext_map(R, M, N, i, 0))",
	}),
		"CoLongExactStart at the short exact sequence of Hom complexes (HomComplexesExact); ext "+
			"is its cohomology (ExtAsCohomology) and ext_map the map composition induces (ExtMapDef)"),
})}

// ExtLongExactMiddle — the long exact sequence at Ext^n(M, N).
var ExtLongExactMiddle = extLongExactMiddleThm{family.Add(registry.ProofEntry{
	Name: "ExtLongExactMiddle",
	Key:  "prop_f27ff688ac77446e",
	Deps: []registry.EntryLike{
		extZeroDef,
		ExtMapDef,
		ExtConnectingDef,
		module_homomorphism.ShortExactModules,
		ExtAsCohomology,
		HomComplexesExact,
		chain_complex.CoLongExactMiddle,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(ext_zero(R, M, N'', n), " +
			"    ext(R, M, N', n), " +
			"    ext(R, M, N, n), " +
			"    ext_map(R, M, N, i, n), " +
			"    ext_map(R, M, N'', p, n))",
	}),
		"CoLongExactMiddle at the short exact sequence of Hom complexes (HomComplexesExact); ext "+
			"is its cohomology (ExtAsCohomology) and ext_map the map composition induces (ExtMapDef)"),
})}

// ExtLongExactQuotient — the long exact sequence at Ext^n(M, N”):
// p's map followed by the connecting map.
var ExtLongExactQuotient = extLongExactQuotientThm{family.Add(registry.ProofEntry{
	Name: "ExtLongExactQuotient",
	Key:  "prop_8e953f158ef3bd76",
	Deps: []registry.EntryLike{
		extZeroDef,
		ExtMapDef,
		ExtConnectingDef,
		module_homomorphism.ShortExactModules,
		ExtAsCohomology,
		HomComplexesExact,
		chain_complex.CoLongExactQuotient,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(ext_zero(R, M, N', n + 1), " +
			"    ext(R, M, N, n), " +
			"    ext(R, M, N'', n), " +
			"    ext_map(R, M, N'', p, n), " +
			"    ext_connecting(R, M, N', N, i, p, n))",
	}),
		"CoLongExactQuotient at the short exact sequence of Hom complexes"),
})}

// ExtLongExactSub — the long exact sequence at Ext^(n+1)(M, N'): the
// connecting map followed by i's map.
var ExtLongExactSub = extLongExactSubThm{family.Add(registry.ProofEntry{
	Name: "ExtLongExactSub",
	Key:  "prop_c24e2aec80505de4",
	Deps: []registry.EntryLike{
		extZeroDef,
		ExtMapDef,
		ExtConnectingDef,
		module_homomorphism.ShortExactModules,
		ExtAsCohomology,
		HomComplexesExact,
		chain_complex.CoLongExactSub,
		chain_complex.CoconnectingHom,
	},
	Build: family.Card(module_homomorphism.ShortExactModules.Statement(Statement{
		Binders: "∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "exact_at(ext_zero(R, M, N, n + 1), " +
			"    ext(R, M, N'', n), " +
			"    ext(R, M, N', n + 1), " +
			"    ext_connecting(R, M, N', N, i, p, n), " +
			"    ext_map(R, M, N, i, n + 1))",
	}),
		"CoLongExactSub at the short exact sequence of Hom complexes"),
})}
