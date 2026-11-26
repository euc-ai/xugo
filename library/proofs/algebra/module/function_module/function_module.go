// function_module.go — functions on a set of generators with values in
// a module N, added, negated and scaled pointwise. Those that vanish off
// the set form the module function_module(N, S), the homomorphisms out of
// the free module on S read at the generators; those of finite support,
// finite_supp(N.zero, N.carrier, S), a submodule of it, the module
// finite_supp_module(N, S), the free module on S tensored with N. With N
// the ring itself, the finitely supported functions are the free module.
// Homomorphisms of N into a module P, one at each point of S, sum over the
// support of a function to a homomorphism out of finite_supp_module(N, S).

package function_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Functions of finite support, added pointwise
// ---------------------------------------------------------------------------

// FiniteSupportDef — `finite_support(zero, f)`: f is zero off a finite set.
var FiniteSupportDef = finiteSupportDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteSupportDef",
	Key:   "prop_aea5a64fb5eb94c5",
	Const: "finite_support",
	Type:  "A → (D → A) → bool",
	Equations: []string{
		"∀zero:A. ∀f:(D → A). finite_support(zero, f) ⇔ finite(fun_support(zero, f))",
	},
})}

// FiniteSupportEventuallyConstant — a function of finite support is
// eventually constant: off its support, a finite set, it takes the value
// zero.
var FiniteSupportEventuallyConstant = finiteSupportEventuallyConstantThm{family.Add(registry.ProofEntry{
	Name: "FiniteSupportEventuallyConstant",
	Key:  "prop_53ad906e3e5d29cb",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀f:(D → A).",
		Hypotheses: []string{
			"finite_support(zero, f)",
		},
		Conclusion: "eventually_constant(f)",
	},
		func(a *Argument, zero *Expr[A], f *Arrow[D, A], support Fact) {
			a.Show(
				"zero is a value f takes off a finite set: f differs from zero only on its support",
				Simp(Fwd(cardinal.EventuallyConstantDef)),
				Witness(zero),
				By(support, FiniteSupportDef))
		}),
})}

// FunAddDef — pointwise addition of functions, by the addition of their
// codomain (the ring's for a free module, a module's for a function module).
var FunAddDef = funAddDefThm{family.Define(registry.DefEntry{
	Name:     "FunAddDef",
	Key:      "prop_1e734f1f8b126285",
	Const:    "fun_add",
	Type:     "(A → A → A) → (D → A) → (D → A) → D → A",
	Implicit: []string{"add"},
	Equations: []string{
		"∀add:(A → A → A). ∀f g:(D → A). ∀x:D. fun_add(add, f, g, x) = add(f(x), g(x))",
	},
})}

// FunZeroDef — the zero function.
var FunZeroDef = funZeroDefThm{family.Define(registry.DefEntry{
	Name:      "FunZeroDef",
	Key:       "prop_2878f4f70706258",
	Const:     "fun_zero",
	Type:      "A → D → A",
	Implicit:  []string{"zero"},
	Equations: []string{"∀zero:A. ∀x:D. fun_zero(zero, x) = zero"},
})}

// FunNegDef — pointwise negation.
var FunNegDef = funNegDefThm{family.Define(registry.DefEntry{
	Name:      "FunNegDef",
	Key:       "prop_c4b61c60e7cc9ab7",
	Const:     "fun_neg",
	Type:      "(A → A) → (D → A) → D → A",
	Implicit:  []string{"neg"},
	Equations: []string{"∀neg:(A → A). ∀f:(D → A). ∀x:D. fun_neg(neg, f, x) = neg(f(x))"},
})}

// FunSmulDef — pointwise scaling of a function into a module by a ring
// element; the free module scales its ring-valued functions by the
// ring's product, the case where the module is the ring.
var FunSmulDef = funSmulDefThm{family.Define(registry.DefEntry{
	Name:     "FunSmulDef",
	Key:      "prop_74d91576537929db",
	Const:    "fun_smul",
	Type:     "(A → C → C) → A → (D → C) → D → C",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → C → C). ∀r:A. ∀f:(D → C). ∀x:D. fun_smul(mul, r, f, x) = mul(r, f(x))",
	},
})}

// ---------------------------------------------------------------------------
// Modules of functions
// ---------------------------------------------------------------------------

// FiniteSuppDef — `finite_supp(zero, c, S)`: the c-valued functions on
// the index type of finite support, zero off S. At a ring's zero and
// carrier it is the free module on S; at a module N's,
// `finite_supp(N.zero, N.carrier, S)`, the finitely supported N-valued
// functions on S.
var FiniteSuppDef = finiteSuppDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteSuppDef",
	Key:   "prop_476ebdf794a249f",
	Const: "finite_supp",
	Type:  "C → set(C) → set(D) → set(D → C)",
	Equations: []string{
		"∀zero:C. ∀c:set(C). ∀S:set(D). " +
			"    finite_supp(zero, c, S) = " +
			"    {f:(D → C) | finite_support(zero, f) ∧ (∀x:D. f(x) ∈ c) ∧ (∀x:D. x ∉ S ⇒ f(x) = zero)}",
	},
	Deps: []registry.EntryLike{FiniteSupportDef},
})}

// FiniteSuppMember — a function lies in finite_supp(zero, c, S) exactly
// when its support is a finite part of S and its values lie in c: the
// definition, with "zero off S" read as the support lying inside S.
var FiniteSuppMember = finiteSuppMemberThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppMember",
	Key:  "prop_6494033c593ea0be",
	Build: family.Theorem("∀zero:C. ∀c:set(C). ∀S:set(D). ∀f:(D → C). "+
		"    f ∈ finite_supp(zero, c, S) ⇔ "+
		"    finite(fun_support(zero, f)) ∧ fun_support(zero, f) ⊆ S ∧ (∀x:D. f(x) ∈ c)",
		func(a *Argument, zero *Expr[C], c *Expr[Set[C]], S *Expr[Set[D]], f *Arrow[D, C]) {
			a.Show(
				"f vanishes off S exactly when every point where it is not zero lies in S",
				Simp(Fwd(FiniteSuppDef), Fwd(FiniteSupportDef)),
				BySets())
		}),
})}

// FiniteSuppCountable — the finitely supported functions on a countable
// set with values in a countable set are countably many: each differs from
// the constant function zero at finitely many points, all of them in S,
// with its values there in c, so they are among the finite modifications of
// that constant function (cardinal.CountableFiniteModifications), which are
// countably many.
var FiniteSuppCountable = finiteSuppCountableThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppCountable",
	Key:  "prop_2bffef56a41282d4",
	Build: family.Theorem(Statement{
		Binders:    "∀zero:C. ∀c:set(C). ∀S:set(D).",
		Hypotheses: []string{"countable(c)", "countable(S)"},
		Conclusion: "countable(finite_supp(zero, c, S))",
	}, func(a *Argument, zero *Expr[C], c *Expr[Set[C]], S *Expr[Set[D]], given Fact) {
		modifications := a.Have(
			"a finitely supported function differs from zero at "+
				"finitely many points, all in S, and takes its values in c",
			"finite_supp(zero, c, S) ⊆ "+
				"{f:(D → C) | finite({x:D | f(x) ≠ zero}) ∧ (∀x:D. f(x) ≠ zero ⇒ x ∈ S ∧ f(x) ∈ c)}",
			Unfold(set_basic.SubsetDef),
			Simp(Fwd(FiniteSuppMember), Fwd(functions.FunSupportDef)),
			BySets())
		a.Show(
			"inside the countably many finite modifications of the constant "+
				"function zero, the finitely supported functions are countable",
			By(
				given,
				modifications,
				cardinal.CountableFiniteModifications.At(
					S, a.TermAs[Fun[D, C]]("λx:D. zero"), a.TermAs[Fun[D, Set[C]]]("λx:D. c")),
				cardinal.CountableSubset))
	}),
	Reading: "Nothing asks zero to lie in c. With c all the numbers and zero " +
		"0 the set is monomials(S), so a polynomial algebra over a countable ring " +
		"in countably many variables is countable, by this statement applied twice.",
})}

// FunModuleDef — `fun_module(zero, c, S)`: all c-valued functions on
// the index type that are zero off S. A module N's is
// `fun_module(N.zero, N.carrier, S)`.
var FunModuleDef = funModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FunModuleDef",
	Key:   "prop_6add625afc0c6554",
	Const: "fun_module",
	Type:  "C → set(C) → set(D) → set(D → C)",
	Equations: []string{
		"∀zero:C. ∀c:set(C). ∀S:set(D). " +
			"    fun_module(zero, c, S) = {g:(D → C) | (∀x:D. g(x) ∈ c) ∧ (∀x:D. x ∉ S ⇒ g(x) = zero)}",
	},
})}

// FiniteSuppModuleDef — `finite_supp_module(N, S)`: the finitely
// supported N-valued functions on S as a module record, N's operations
// read pointwise.
var FiniteSuppModuleDef = finiteSuppModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteSuppModuleDef",
	Const: "finite_supp_module",
	Type:  "module_ops(A, C) → set(I) → module_ops(A, I → C)",
	Key:   "prop_2e01f7e08174e68f",
	Equations: []string{
		"∀N:module_ops(A, C). ∀S:set(I). " +
			"    finite_supp_module(N, S) = " +
			"    mk_module(fun_add⟨D:I⟩(N.add), " +
			"        fun_zero⟨D:I⟩(N.zero), " +
			"        fun_neg⟨D:I⟩(N.neg), " +
			"        fun_smul⟨D:I⟩(N.smul), " +
			"        finite_supp(N.zero, N.carrier, S))",
	},
	Deps: []registry.EntryLike{FiniteSuppDef, FunAddDef, FunZeroDef, FunNegDef, FunSmulDef},
})}

// FunctionModuleDef — `function_module(N, S)`: all N-valued functions
// that vanish off S as a module record, N's operations read pointwise;
// no finiteness is asked of their support.
var FunctionModuleDef = functionModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FunctionModuleDef",
	Const: "function_module",
	Type:  "module_ops(A, C) → set(I) → module_ops(A, I → C)",
	Key:   "prop_3ca9d35be6e31f3",
	Equations: []string{
		"∀N:module_ops(A, C). ∀S:set(I). " +
			"    function_module(N, S) = " +
			"    mk_module(fun_add⟨D:I⟩(N.add), " +
			"        fun_zero⟨D:I⟩(N.zero), " +
			"        fun_neg⟨D:I⟩(N.neg), " +
			"        fun_smul⟨D:I⟩(N.smul), " +
			"        fun_module(N.zero, N.carrier, S))",
	},
	Deps: []registry.EntryLike{FunModuleDef, FunAddDef, FunZeroDef, FunNegDef, FunSmulDef},
})}

// FunModuleOn — the functions into a module M that vanish off S form a
// module over M's ring, M's operations read at each point. Each module
// law is M's own law at every x, where the values lie in M's carrier.
// The functions are closed under the operations because each keeps the
// values in M's carrier, by M's closure laws, and keeps them zero off
// S: zero + zero, the negation of zero and c • zero are all zero.
var FunModuleOn = funModuleOnThm{family.Add(registry.ProofEntry{
	Name: "FunModuleOn",
	Key:  "prop_51c459cf23692839",
	Build: module.ModuleOn.Law("∀S:set(D). module_on(R, function_module(M, S))",
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], S *Expr[Set[D]]) {
			// M's vectors are a group on its carrier under the vector
			// addition, where the group laws are read point by point.
			additive := module.AddGroupOn.Read(ambient)
			zeroVector := group.OneIn.Read(additive)

			member := a.Have(
				"a member is a function valued in M and zero off S",
				"∀f:(D → B). "+
					"    f ∈ fun_module(M.zero, M.carrier, S) ⇔ "+
					"    (∀x:D. f(x) ∈ M.carrier) ∧ (∀x:D. x ∉ S ⇒ f(x) = M.zero)",
				Simp(Fwd(FunModuleDef)),
				BySets())
			values := a.Have(
				"so every value of a member lies in M",
				"∀f:(D → B). ∀x:D. f ∈ fun_module(M.zero, M.carrier, S) ⇒ f(x) ∈ M.carrier",
				By(member))

			// The group under pointwise addition: the zero function, sums and
			// negations stay members, and the group laws are M's at every
			// point.
			zeroIn := a.Have(
				"the zero function is a member, its one value being M's zero",
				"fun_zero(M.zero) ∈ fun_module(M.zero, M.carrier, S)",
				By(member, FunZeroDef, zeroVector))
			addIn := a.Have(
				"a sum of members is a member",
				Statement{
					Binders: "∀u v:(D → B).",
					Hypotheses: []string{
						"u ∈ fun_module(M.zero, M.carrier, S)",
						"v ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_add(u, v) ∈ fun_module(M.zero, M.carrier, S)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[D, B]](), b.FixAs[Fun[D, B]]()
					members := b.Assume()
					inM := b.Have(
						"its values are sums in M",
						"∀x:D. fun_add(u, v, x) ∈ M.carrier",
						Simp(Fwd(FunAddDef)),
						By(values, members, group.MulIn.Read(additive)))
					offS := b.Have(
						"off S it is zero + zero, which is zero",
						"∀x:D. x ∉ S ⇒ fun_add(u, v, x) = M.zero",
						Simp(Fwd(FunAddDef)),
						By(
							member.At(u),
							member.At(v),
							members,
							group.LeftIdentityOn.Read(additive).AsFact().At(b.TermAs[B]("M.zero")),
							zeroVector))
					b.Show(
						"so the sum is a member",
						By(member, inM, offS))
				}))
			negIn := a.Have(
				"a negation of a member is a member",
				"∀u:(D → B). u ∈ fun_module(M.zero, M.carrier, S) ⇒ fun_neg(u) ∈ fun_module(M.zero, M.carrier, S)",
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[D, B]]()
					uIn := b.Assume()
					inM := b.Have(
						"its values are negations in M",
						"∀x:D. fun_neg(u, x) ∈ M.carrier",
						Simp(Fwd(FunNegDef)),
						By(values, uIn, group.InvIn.Read(additive)))
					offS := b.Have(
						"off S it is the negation of zero, which is zero",
						"∀x:D. x ∉ S ⇒ fun_neg(u, x) = M.zero",
						Simp(Fwd(FunNegDef)),
						By(member.At(u), uIn, group.InvOneOn.Read(additive)))
					b.Show(
						"so the negation is a member",
						By(member, inM, offS))
				}))
			assoc := a.Have(
				"pointwise addition associates, as M's addition does at every point",
				Statement{
					Binders: "∀u v w:(D → B).",
					Hypotheses: []string{
						"u ∈ fun_module(M.zero, M.carrier, S)",
						"v ∈ fun_module(M.zero, M.carrier, S)",
						"w ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_add(u, fun_add(v, w)) = fun_add(fun_add(u, v), w)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]()
					b.FixAs[Fun[D, B]]()
					b.FixAs[Fun[D, B]]()
					members := b.Assume()
					b.Show(
						"at each x it is u(x) + (v(x) + w(x)) = (u(x) + v(x)) + w(x)",
						Funext(),
						Simp(Fwd(FunAddDef)),
						By(values, members, group.AssocOn.Read(additive)))
				}))
			leftZero := a.Have(
				"the zero function is a left identity, as M's zero is",
				"∀u:(D → B). u ∈ fun_module(M.zero, M.carrier, S) ⇒ fun_add(fun_zero(M.zero), u) = u",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]()
					uIn := b.Assume()
					b.Show(
						"at each x it is zero + u(x) = u(x)",
						Funext(),
						Simp(Fwd(FunAddDef), Fwd(FunZeroDef)),
						By(values, uIn, group.LeftIdentityOn.Read(additive)))
				}))
			leftNeg := a.Have(
				"the pointwise negation is a left inverse, as M's negation is",
				"∀u:(D → B). u ∈ fun_module(M.zero, M.carrier, S) ⇒ fun_add(fun_neg(u), u) = fun_zero(M.zero)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]()
					uIn := b.Assume()
					b.Show(
						"at each x it is -u(x) + u(x) = zero",
						Funext(),
						Simp(Fwd(FunAddDef), Fwd(FunNegDef), Fwd(FunZeroDef)),
						By(values, uIn, group.LeftInverseOn.Read(additive)))
				}))
			vectors := a.Have(
				"the members are a group under pointwise addition",
				"group_on(module_additive_group(function_module(M, S)))",
				Simp(Fwd(module_record.ModuleAdditiveGroupDef), Fwd(FunctionModuleDef)),
				By(zeroIn, addIn, negIn, assoc, leftZero, leftNeg, group.GroupOn))

			// The rest of a module: the scalars are M's ring, the addition
			// commutes, scaling keeps a member a member, and the scaling laws
			// are M's at every point.
			ring := a.Have(
				"the scalars are M's ring",
				"comm_ring_on(R)",
				By(module.RingOn.Read(ambient)))
			commutes := a.Have(
				"pointwise addition commutes, as M's addition does",
				Statement{
					Binders: "∀u v:(D → B).",
					Hypotheses: []string{
						"u ∈ fun_module(M.zero, M.carrier, S)",
						"v ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_add(u, v) = fun_add(v, u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]()
					b.FixAs[Fun[D, B]]()
					members := b.Assume()
					b.Show(
						"at each x it is u(x) + v(x) = v(x) + u(x)",
						Funext(),
						Simp(Fwd(FunAddDef)),
						By(values, members, module.AddComm.Read(ambient)))
				}))
			scaled := a.Have(
				"a scaled member is a member",
				Statement{
					Binders: "∀c:A. ∀u:(D → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_smul(M.smul, c, u) ∈ fun_module(M.zero, M.carrier, S)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A](), b.FixAs[Fun[D, B]]()
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u is a member")
					scalar, uIn := b.MemberOf[on.R](c, given[0]), given[1]
					inM := b.Have(
						"its values are scalings in M",
						"∀x:D. fun_smul(M.smul, c, u, x) ∈ M.carrier",
						Simp(Fwd(FunSmulDef)),
						By(values, uIn, scalar, module.SmulIn.Read(ambient)))
					offS := b.Have(
						"off S it is c • zero, which is zero",
						"∀x:D. x ∉ S ⇒ fun_smul(M.smul, c, u, x) = M.zero",
						Simp(Fwd(FunSmulDef)),
						By(member.At(u), uIn, module.SmulZero.Read(ambient).At(scalar)))
					b.Show(
						"so the scaled function is a member",
						By(member, inM, offS))
				}))
			distributes := a.Have(
				"a scalar distributes over a sum, as it does over a sum in M",
				Statement{
					Binders: "∀c:A. ∀u v:(D → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ fun_module(M.zero, M.carrier, S)",
						"v ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_smul(M.smul, c, fun_add(u, v)) = " +
						"fun_add(fun_smul(M.smul, c, u), fun_smul(M.smul, c, v))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					b.FixAs[Fun[D, B]]()
					b.FixAs[Fun[D, B]]()
					given := b.Assume()
					b.Show(
						"at each x it is c • (u(x) + v(x)) = c • u(x) + c • v(x)",
						Funext(),
						Simp(Fwd(FunAddDef), Fwd(FunSmulDef)),
						By(values, given, module.SmulAddLeft.Read(ambient)))
				}))
			sums := a.Have(
				"a sum of scalars distributes over a function, as it does over a vector",
				Statement{
					Binders: "∀c d:A. ∀u:(D → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"d ∈ R.carrier",
						"u ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_smul(M.smul, c + d, u) = fun_add(fun_smul(M.smul, c, u), fun_smul(M.smul, d, u))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					b.FixAs[A]()
					b.FixAs[Fun[D, B]]()
					given := b.Assume()
					b.Show(
						"at each x it is (c + d) • u(x) = c • u(x) + d • u(x)",
						Funext(),
						Simp(Fwd(FunAddDef), Fwd(FunSmulDef)),
						By(values, given, module.SmulAddRight.Read(ambient)))
				}))
			products := a.Have(
				"scaling by a product is scaling twice, as it is in M",
				Statement{
					Binders: "∀c d:A. ∀u:(D → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"d ∈ R.carrier",
						"u ∈ fun_module(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_smul(M.smul, c * d, u) = fun_smul(M.smul, c, fun_smul(M.smul, d, u))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					b.FixAs[A]()
					b.FixAs[Fun[D, B]]()
					given := b.Assume()
					b.Show(
						"at each x it is (c * d) • u(x) = c • (d • u(x))",
						Funext(),
						Simp(Fwd(FunSmulDef)),
						By(values, given, module.SmulMul.Read(ambient)))
				}))
			one := a.Have(
				"the ring's one fixes every function, as it fixes every vector",
				"∀u:(D → B). u ∈ fun_module(M.zero, M.carrier, S) ⇒ fun_smul(M.smul, R.one, u) = u",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]()
					uIn := b.Assume()
					b.Show(
						"at each x it is one • u(x) = u(x)",
						Funext(),
						Simp(Fwd(FunSmulDef)),
						By(values, uIn, module.SmulOne.Read(ambient)))
				}))
			a.Show(
				"so the functions vanishing off S, with the pointwise operations, "+
					"are a module over R: unfolded, module_on asks the eight facts above",
				Unfold(module.ModuleOn),
				By(ring, vectors, commutes, scaled, distributes, sums, products, one))
		}),
})}

// ModuleSumApply — a sum of functions into a module, under the pointwise
// operations, evaluates pointwise. The functions on E into M are a module
// under the pointwise operations, and evaluation at y sends its zero to
// M's zero and its sum of two functions to the sum of their values, so it
// carries the finite sum of the G(x) to the sum of the G(x, y).
var ModuleSumApply = moduleSumApplyThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumApply",
	Key:  "prop_18e57ba276ccd729",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀G:(D → E → B). ∀y:E.",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. ∀z:E. x ∈ s ⇒ G(x, z) ∈ M.carrier",
		},
		Conclusion: "module_sum(fun_add⟨D:E⟩(M.add), fun_zero⟨D:E⟩(M.zero), s, G, y) = " +
			"module_sum(M.add, M.zero, s, λx:D. G(x, y))",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			G *Arrow[D, Fun[E, B]],
			y *Expr[E],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"each G(x) with x in s takes its values in M")
			finite, values := parts[0], parts[1]
			add, zero, carrier := a.TermAs[Op[B]]("M.add"), a.TermAs[B]("M.zero"), a.TermAs[Set[B]]("M.carrier")
			universe := a.TermAs[Set[E]]("𝕌")
			functions := a.Have(
				"the functions on E into M are a module over R under the pointwise operations",
				"module_on(R, function_module(M, 𝕌⟨A:E⟩))",
				By(FunModuleOn.Read(ambient)))
			additive := module.AddMonoidOn.Read(functions)
			members := a.Have(
				"each G(x) with x in s is one of them",
				"∀x:D. x ∈ s ⇒ G(x) ∈ fun_module(M.zero, M.carrier, 𝕌)",
				BySets(values, FunModuleDef.At(zero, carrier, universe)))
			evaluation := a.TermAs[Fun[Fun[E, B], B]]("λg:(E → B). g(y)")
			atZero := a.Have(
				"evaluation at y sends the zero function to M.zero",
				"fun_zero(M.zero, y) = M.zero",
				Cite(FunZeroDef))
			atSum := a.Have(
				"and a pointwise sum to the sum of the values",
				"∀f g:(E → B). fun_add(f, g, y) = f(y) + g(y)",
				Cite(FunAddDef))
			a.Show(
				"so evaluation at y is a homomorphism of the additive monoids, and it carries the sum",
				By(
					module.ModuleSumMonoidHomomorphism.Read(additive).At(add, zero, evaluation, s, G),
					finite,
					members,
					atZero,
					atSum))
		}),
})}

// FiniteSuppSubmodule — among the functions into M that vanish off S,
// those of finite support are a submodule. The functions vanishing off S
// are a module, so a sum, a negation or a scaling of members vanishes off
// S, and what is left is the finiteness of its support. A function that
// vanishes wherever two members both vanish has its support inside the
// union of theirs, so a finite support. Each pointwise operation keeps
// M's zero, so a sum (and, taking u = v, a negation or a scaling)
// satisfies it; the zero function has empty support.
var FiniteSuppSubmodule = finiteSuppSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppSubmodule",
	Key:  "prop_f182a00c55345b0b",
	Build: module.ModuleOn.Law("∀S:set(D). "+
		"    submodule(R, function_module(M, S), finite_supp(M.zero, M.carrier, S))",
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], S *Expr[Set[D]]) {
			// M's additive group on its carrier, where a value of a pointwise
			// operation is read, and the module of functions vanishing off S,
			// whose operations keep a function vanishing off S.
			additive := module.AddGroupOn.Read(ambient)
			functionModule := a.Have(
				"the functions into M that vanish off S are a module over R",
				"module_on(R, function_module(M, S))",
				By(FunModuleOn, ambient))
			pointwise := module.AddGroupOn.Read(functionModule)

			member := a.Have(
				"a member is a function vanishing off S whose support is finite",
				"∀f:(D → B). "+
					"    f ∈ finite_supp(M.zero, M.carrier, S) ⇔ "+
					"    f ∈ fun_module(M.zero, M.carrier, S) ∧ finite(fun_support(M.zero, f))",
				Simp(Fwd(FiniteSuppMember), Fwd(FunModuleDef)),
				BySets())
			dominated := a.Have(
				"a function that vanishes wherever two members both vanish has finite support",
				Statement{
					Binders: "∀u v w:(D → B).",
					Hypotheses: []string{
						"u ∈ finite_supp(M.zero, M.carrier, S)",
						"v ∈ finite_supp(M.zero, M.carrier, S)",
						"∀x:D. u(x) = M.zero ∧ v(x) = M.zero ⇒ w(x) = M.zero",
					},
					Conclusion: "finite(fun_support(M.zero, w))",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[D, B]](), b.FixAs[Fun[D, B]]()
					b.FixAs[Fun[D, B]]()
					parts := b.Conjuncts(
						b.Assume(),
						"u is a member",
						"v is a member",
						"w vanishes where u and v do")
					uIn, vIn, vanishing := parts[0], parts[1], parts[2]
					suppU, suppV :=
						b.TermAs[Set[D]]("fun_support(M.zero, u)"), b.TermAs[Set[D]]("fun_support(M.zero, v)")
					suppW, union :=
						b.TermAs[Set[D]]("fun_support(M.zero, w)"),
						b.TermAs[Set[D]]("fun_support(M.zero, u) ∪ fun_support(M.zero, v)")
					inUnion := b.Have(
						"the support of w lies in the union of the supports of u and v",
						"fun_support(M.zero, w) ⊆ fun_support(M.zero, u) ∪ fun_support(M.zero, v)",
						BySets(vanishing))
					b.Show(
						"so it is finite, the supports of u and v being finite",
						By(
							member.At(u),
							member.At(v),
							uIn,
							vIn,
							inUnion,
							finite_set.FiniteSubset.At(suppW, union),
							finite_set.FiniteUnion.At(suppU, suppV)))
				}))

			// A subgroup of the functions vanishing off S under the pointwise
			// addition: the members lie among them, and the zero function,
			// sums and negations stay members.
			inFunctions := a.Have(
				"so a member is a function vanishing off S",
				"∀f:(D → B). f ∈ finite_supp(M.zero, M.carrier, S) ⇒ f ∈ fun_module(M.zero, M.carrier, S)",
				a.ForEach(func(f *Expr[Fun[D, B]]) Action { return By(member.At(f)) }))
			zeroFunction := a.TermAs[Fun[D, B]]("fun_zero(M.zero)")
			emptySupport := a.Have(
				"the zero function has empty support",
				"finite(fun_support(M.zero, λx:D. fun_zero(M.zero, x)))",
				Unfold(functions.FunSupportDef),
				Simp(Fwd(FunZeroDef)),
				BySets(finite_set.FiniteRules))
			zeroIn := a.Have(
				"so it is a member, the zero of the functions vanishing off S",
				"fun_zero(M.zero) ∈ finite_supp(M.zero, M.carrier, S)",
				By(member.At(zeroFunction), group.OneIn.Read(pointwise), emptySupport))
			addIn := a.Have(
				"a sum of members is a member",
				Statement{
					Binders: "∀u v:(D → B).",
					Hypotheses: []string{
						"u ∈ finite_supp(M.zero, M.carrier, S)",
						"v ∈ finite_supp(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_add(M.add, u, v) ∈ finite_supp(M.zero, M.carrier, S)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[D, B]](), b.FixAs[Fun[D, B]]()
					members := b.Assume()
					vanishes := b.Have(
						"where u and v vanish it is zero + zero, which is zero",
						"∀x:D. u(x) = M.zero ∧ v(x) = M.zero ⇒ fun_add(M.add, u, v, x) = M.zero",
						Derive(func(e *Argument) {
							e.FixAs[D]()
							zeros := e.Conjuncts(
								e.Assume(),
								"u vanishes at x",
								"v vanishes at x")
							e.Show(
								"the value u(x) + v(x) is zero + zero",
								Simp(Fwd(FunAddDef)),
								zeros[0].Rw(),
								zeros[1].Rw(),
								By(
									group.LeftIdentityOn.Read(additive).AsFact().At(e.TermAs[B]("M.zero")),
									group.OneIn.Read(additive)))
						}))
					sum := b.TermAs[Fun[D, B]]("fun_add(M.add, u, v)")
					finite := b.Have(
						"so its support is finite, inside the union of the supports of u and v",
						"finite(fun_support(M.zero, λx:D. fun_add(M.add, u, v, x)))",
						By(dominated.At(u, v, sum), members, vanishes))
					b.Show(
						"and a sum of functions vanishing off S vanishes off S, so with its finite support it is a member",
						By(member.At(sum), members, inFunctions, group.MulIn.Read(pointwise), finite))
				}))
			negIn := a.Have(
				"a negation of a member is a member",
				Statement{
					Binders: "∀u:(D → B).",
					Hypotheses: []string{
						"u ∈ finite_supp(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_neg(M.neg, u) ∈ finite_supp(M.zero, M.carrier, S)",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[D, B]]()
					uIn := b.Assume()
					vanishes := b.Have(
						"where u vanishes it is the negation of zero, which is zero",
						"∀x:D. u(x) = M.zero ⇒ fun_neg(M.neg, u, x) = M.zero",
						Derive(func(e *Argument) {
							e.FixAs[D]()
							zero := e.Assume()
							e.Show(
								"the value -u(x) is the negation of zero",
								Simp(Fwd(FunNegDef)),
								zero.Rw(),
								Cite(group.InvOneOn.Read(additive)))
						}))
					negation := b.TermAs[Fun[D, B]]("fun_neg(M.neg, u)")
					finite := b.Have(
						"so its support is finite, inside the support of u",
						"finite(fun_support(M.zero, λx:D. fun_neg(M.neg, u, x)))",
						By(dominated.At(u, u, negation), uIn, vanishes))
					b.Show(
						"and a negation of a function vanishing off S vanishes "+
							"off S, so with its finite support it is a member",
						By(member.At(negation), uIn, inFunctions, group.InvIn.Read(pointwise), finite))
				}))
			subgroup := a.Have(
				"so the members are a subgroup of the functions vanishing off S under pointwise addition",
				"subgroup(mk_group(fun_add(M.add), "+
					"        fun_zero(M.zero), "+
					"        fun_neg(M.neg), "+
					"        fun_module(M.zero, M.carrier, S)), "+
					"    finite_supp(M.zero, M.carrier, S))",
				By(inFunctions, zeroIn, addIn, negIn, group.SubgroupDef, set_basic.SubsetDef))

			// Scaling keeps a member a member: c • zero is zero.
			smulIn := a.Have(
				"a scaled member is a member",
				Statement{
					Binders: "∀c:A. ∀u:(D → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ finite_supp(M.zero, M.carrier, S)",
					},
					Conclusion: "fun_smul(M.smul, c, u) ∈ finite_supp(M.zero, M.carrier, S)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A](), b.FixAs[Fun[D, B]]()
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u is a member")
					scalar, uIn := b.MemberOf[on.R](c, given[0]), given[1]
					vanishes := b.Have(
						"where u vanishes it is c • zero, which is zero",
						"∀x:D. u(x) = M.zero ⇒ fun_smul(M.smul, c, u, x) = M.zero",
						Derive(func(e *Argument) {
							e.FixAs[D]()
							zero := e.Assume()
							e.Show(
								"the value c • u(x) is c • zero",
								Simp(Fwd(FunSmulDef)),
								zero.Rw(),
								By(module.SmulZero.Read(ambient).At(scalar)))
						}))
					scaled := b.TermAs[Fun[D, B]]("fun_smul(M.smul, c, u)")
					finite := b.Have(
						"so its support is finite, inside the support of u",
						"finite(fun_support(M.zero, λx:D. fun_smul(M.smul, c, u, x)))",
						By(dominated.At(u, u, scaled), uIn, vanishes))
					b.Show(
						"and a scaling of a function vanishing off S vanishes "+
							"off S, so with its finite support it is a member",
						By(member.At(scaled), scalar, uIn, inFunctions, module.SmulIn.Read(functionModule), finite))
				}))
			a.Show(
				"a subgroup of the function module's vectors closed under its scaling is a submodule",
				Simp(Fwd(submodule.SubmoduleDef), Fwd(module_record.ModuleAdditiveGroupDef)),
				By(subgroup, smulIn))
		}),
})}

// FiniteSuppModuleOn — the finitely supported functions into a module form
// a module under the pointwise operations: finite_supp_module(M, S) is the
// module of the functions vanishing off S restricted to them, and they
// are a submodule of it.
var FiniteSuppModuleOn = finiteSuppModuleOnThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppModuleOn",
	Key:  "prop_1d03d9dbff180686",
	Build: module.ModuleOn.Law("∀S:set(D). module_on(R, finite_supp_module(M, S))",
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], S *Expr[Set[D]]) {
			restricted := a.Have(
				"both are M's operations read pointwise, so finite_supp_module(M, "+
					"S) is function_module(M, S) on the finitely supported functions",
				"finite_supp_module(M, S) = "+
					"restrict_module(function_module(M, S), finite_supp(M.zero, M.carrier, S))",
				Simp(Fwd(FiniteSuppModuleDef), Fwd(module_record.RestrictModuleDef), Fwd(FunctionModuleDef)),
				Refl())
			functions := a.Have(
				"the functions into M that vanish off S are a module over R",
				"module_on(R, function_module(M, S))",
				By(FunModuleOn, ambient))
			a.Show(
				"the finitely supported ones are a submodule of it, so a module on their own",
				restricted.Rw(),
				By(submodule.SubmoduleModuleOn.Read(functions), FiniteSuppSubmodule, ambient))
		}),
})}

// ---------------------------------------------------------------------------
// Sums over the support
// ---------------------------------------------------------------------------

// FiniteSuppSumHom — homomorphisms T(x) of N into P, one at each point x
// of S, sum to a homomorphism of the finitely supported functions on S
// into P: g ↦ Σ T(x, g(x)) over the support of g. The sum may run over
// any finite part of S outside which g vanishes, each further term being
// T(x, N.zero) = P.zero. Over the union of the supports of u and v each
// term of u + v splits, T(x) being additive, and the sum splits with
// them; each term of c • u is c • T(x, u(x)), and c comes out of the
// sum.
var FiniteSuppSumHom = finiteSuppSumHomThm{family.Add(registry.ProofEntry{
	Name: "FiniteSuppSumHom",
	Key:  "prop_775db66316872a8b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀N:module_ops(A, B). ∀P:module_ops(A, C). ∀S:set(D). ∀T:(D → B → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_on(R, P)",
			"∀x:D. x ∈ S ⇒ module_homomorphism(R, N, P, T(x))",
		},
		Conclusion: "module_homomorphism(R, " +
			"    finite_supp_module(N, S), " +
			"    P, " +
			"    λg:(D → B). module_sum(P.add, P.zero, fun_support(N.zero, g), λx:D. T(x, g(x))))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			N *Expr[ModuleOps[A, B]],
			P *Expr[ModuleOps[A, C]],
			S *Expr[Set[D]],
			T *Arrow[D, Fun[B, C]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"N is a module over R",
				"so is P",
				"at each point x of S, T(x) is a homomorphism of N into P")
			moduleN, moduleP, linear := parts[0], parts[1], parts[2]
			additive := module.AddGroupOn.Read(moduleN)

			// What a homomorphism T(x) does to the values of a function.
			images := a.Have(
				"at a point x of S, T(x) carries N into P",
				"∀x:D. ∀u:B. x ∈ S ∧ u ∈ N.carrier ⇒ T(x, u) ∈ P.carrier",
				Derive(func(b *Argument) {
					x, u := b.FixAs[D]("x"), b.FixAs[B]("u")
					b.Show(
						"T(x) is a homomorphism of N into P",
						By(linear.At(x), module_homomorphism.HomIn.At(R, N, P, T.Apply(x), u)))
				}))
			zeros := a.Have(
				"and N's zero to P's",
				"∀x:D. x ∈ S ⇒ T(x, N.zero) = P.zero",
				a.ForEach(func(x *Expr[D]) Action {
					return By(linear.At(x), module_homomorphism.HomZero.At(R, N, P, T.Apply(x)))
				}))
			sums := a.Have(
				"and a sum to the sum of the images",
				"∀x:D. ∀u v:B. x ∈ S ∧ u ∈ N.carrier ∧ v ∈ N.carrier ⇒ T(x, u + v) = T(x, u) + T(x, v)",
				Derive(func(b *Argument) {
					x, u, v := b.FixAs[D]("x"), b.FixAs[B]("u"), b.FixAs[B]("v")
					b.Show(
						"T(x), a homomorphism, is additive",
						By(linear.At(x), module_homomorphism.HomAdd.At(R, N, P, T.Apply(x), u, v)))
				}))
			scalings := a.Have(
				"and a scaling to the scaling of the image",
				"∀x:D. ∀c:A. ∀u:B. x ∈ S ∧ c ∈ R.carrier ∧ u ∈ N.carrier ⇒ T(x, c • u) = c • T(x, u)",
				Derive(func(b *Argument) {
					x, c, u := b.FixAs[D]("x"), b.FixAs[A]("c"), b.FixAs[B]("u")
					b.Show(
						"T(x), a homomorphism, commutes with scaling",
						By(linear.At(x), module_homomorphism.HomSmul.At(R, N, P, T.Apply(x), c, u)))
				}))

			// The image of g, a sum over the support of g, may run over any
			// finite part of S outside which g vanishes.
			sumOver := a.Have(
				"the sum over the support of g is the sum over any finite part s of S outside which g vanishes",
				Statement{
					Binders: "∀g:(D → B). ∀s:set(D).",
					Hypotheses: []string{
						"finite(s)",
						"s ⊆ S",
						"∀x:D. g(x) ∈ N.carrier",
						"∀x:D. x ∉ s ⇒ g(x) = N.zero",
					},
					Conclusion: "module_sum(P.add, P.zero, fun_support(N.zero, g), λx:D. T(x, g(x))) = " +
						"module_sum(P.add, P.zero, s, λx:D. T(x, g(x)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]("g")
					s := b.FixAs[Set[D]]("s")
					hypotheses := b.Conjuncts(
						b.Assume(),
						"s is finite",
						"s lies in S",
						"g takes its values in N",
						"g vanishes off s")
					finite, sInside, values, off := hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3]
					inside := b.Have(
						"the support of g lies in s",
						"fun_support(N.zero, g) ⊆ s",
						BySets(off))
					terms := b.Have(
						"each term over s lies in P",
						"∀x:D. x ∈ s ⇒ T(x, g(x)) ∈ P.carrier",
						By(images, values, sInside, set_basic.SubsetDef))
					vanish := b.Have(
						"off the support of g each term over s is P's zero",
						"∀x:D. x ∈ s ∧ x ∉ fun_support(N.zero, g) ⇒ T(x, g(x)) = P.zero",
						Derive(func(c *Argument) {
							c.FixAs[D]("x")
							where := c.Conjuncts(
								c.Assume(),
								"x is a point of s",
								"outside the support of g")
							zero := c.Have(
								"g vanishes at x",
								"g(x) = N.zero",
								BySets(where[1]))
							inS := c.Have(
								"x lies in S",
								"x ∈ S",
								BySets(where[0], sInside))
							c.Show(
								"T(x) keeps zero",
								zero.Rw(),
								By(zeros, inS))
						}))
					b.Show(
						"the terms over s outside the support of g vanish",
						By(
							module.ModuleSumSupport.Read(moduleP).At(
								s, b.TermAs[Set[D]]("fun_support(N.zero, g)"), b.TermAs[Fun[D, C]]("λx:D. T(x, g(x))")),
							finite,
							inside,
							terms,
							vanish))
				}))

			inP := a.Have(
				"the map carries the finitely supported functions on S into P",
				Statement{
					Binders: "∀u:(D → B).",
					Hypotheses: []string{
						"u ∈ finite_supp(N.zero, N.carrier, S)",
					},
					Conclusion: "module_sum(P.add, P.zero, fun_support(N.zero, u), λx:D. T(x, u(x))) ∈ P.carrier",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, B]]("u")
					uParts := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(FiniteSuppMember)),
						"the support of u is finite",
						"and lies in S",
						"u takes its values in N")
					b.Show(
						"each term over the support lies in P, and so does their finite sum",
						By(module.ModuleSumIn.Read(moduleP), uParts[0], images, uParts[1], uParts[2], set_basic.SubsetDef))
				}))

			additiveMap := a.Have(
				"the map is additive: over the union of the two supports each term of u + v splits",
				Statement{
					Binders: "∀u v:(D → B).",
					Hypotheses: []string{
						"u ∈ finite_supp(N.zero, N.carrier, S)",
						"v ∈ finite_supp(N.zero, N.carrier, S)",
					},
					Conclusion: "module_sum(P.add, " +
						"    P.zero, " +
						"    fun_support(N.zero, λx:D. fun_add(u, v, x)), " +
						"    λx:D. T(x, fun_add(u, v, x))) = " +
						"module_sum(P.add, P.zero, fun_support(N.zero, u), λx:D. T(x, u(x))) + " +
						"module_sum(P.add, P.zero, fun_support(N.zero, v), λx:D. T(x, v(x)))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[D, B]]("u")
					v := b.FixAs[Fun[D, B]]("v")
					both := b.Conjuncts(
						b.Assume(),
						"u is a finitely supported function on S",
						"so is v")
					uParts := b.Conjuncts(
						b.Simplified(both[0], Fwd(FiniteSuppMember)),
						"the support of u is finite",
						"and lies in S",
						"u takes its values in N")
					vParts := b.Conjuncts(
						b.Simplified(both[1], Fwd(FiniteSuppMember)),
						"the support of v is finite",
						"and lies in S",
						"v takes its values in N")
					union := b.TermAs[Set[D]]("fun_support(N.zero, u) ∪ fun_support(N.zero, v)")
					finite := b.Have(
						"the union of the two supports is finite",
						"finite(fun_support(N.zero, u) ∪ fun_support(N.zero, v))",
						By(
							uParts[0],
							vParts[0],
							finite_set.FiniteUnion.At(
								b.TermAs[Set[D]]("fun_support(N.zero, u)"), b.TermAs[Set[D]]("fun_support(N.zero, v)"))))
					inside := b.Have(
						"and lies in S",
						"fun_support(N.zero, u) ∪ fun_support(N.zero, v) ⊆ S",
						By(uParts[1], vParts[1], set_order.UnionSubset))
					off := b.Have(
						"off the union both u and v vanish",
						"∀x:D. x ∉ fun_support(N.zero, u) ∪ fun_support(N.zero, v) ⇒ u(x) = N.zero ∧ v(x) = N.zero",
						BySets())

					// u + v as a function on the union, and the terms of its sum.
					sumValues := b.Have(
						"u + v takes its values in N",
						"∀x:D. fun_add(u, v, x) ∈ N.carrier",
						Simp(Fwd(FunAddDef)),
						By(uParts[2], vParts[2], group.MulIn.Read(additive)))
					sumOff := b.Have(
						"and vanishes off the union, N.zero + N.zero being N.zero",
						"∀x:D. x ∉ fun_support(N.zero, u) ∪ fun_support(N.zero, v) ⇒ fun_add(u, v, x) = N.zero",
						Derive(func(c *Argument) {
							x := c.FixAs[D]("x")
							outside := c.Assume()
							zeros := c.Conjuncts(
								c.Have(
									"u and v vanish at x",
									"u(x) = N.zero ∧ v(x) = N.zero",
									By(off.At(x), outside)),
								"u vanishes at x",
								"v vanishes at x")
							c.Show(
								"the value u(x) + v(x) is N.zero + N.zero",
								Simp(Fwd(FunAddDef)),
								zeros[0].Rw(),
								zeros[1].Rw(),
								By(group.LeftIdentityOn.Read(additive), group.OneIn.Read(additive)))
						}))
					splits := b.Have(
						"over the union each term of u + v splits, T(x) being additive",
						Statement{
							Binders: "∀x:D.",
							Hypotheses: []string{
								"x ∈ fun_support(N.zero, u) ∪ fun_support(N.zero, v)",
							},
							Conclusion: "T(x, fun_add(u, v, x)) = T(x, u(x)) + T(x, v(x))",
						},
						Simp(Fwd(FunAddDef)),
						By(sums, inside, uParts[2], vParts[2], set_basic.SubsetDef))
					terms := b.Have(
						"and both parts lie in P",
						Statement{
							Binders: "∀x:D.",
							Hypotheses: []string{
								"x ∈ fun_support(N.zero, u) ∪ fun_support(N.zero, v)",
							},
							Conclusion: "T(x, u(x)) ∈ P.carrier ∧ T(x, v(x)) ∈ P.carrier",
						},
						By(images, inside, uParts[2], vParts[2], set_basic.SubsetDef))
					sumU := b.Have(
						"the sum for u runs over the union",
						"module_sum(P.add, P.zero, fun_support(N.zero, u), λx:D. T(x, u(x))) = "+
							"module_sum(P.add, P.zero, fun_support(N.zero, u) ∪ fun_support(N.zero, v), λx:D. T(x, u(x)))",
						By(sumOver.At(u, union), finite, inside, uParts[2], off))
					sumV := b.Have(
						"and so does the sum for v",
						"module_sum(P.add, P.zero, fun_support(N.zero, v), λx:D. T(x, v(x))) = "+
							"module_sum(P.add, P.zero, fun_support(N.zero, u) ∪ fun_support(N.zero, v), λx:D. T(x, v(x)))",
						By(sumOver.At(v, union), finite, inside, vParts[2], off))
					b.Show(
						"the sum for u + v is the sum of the sums for u and v",
						CalcEq(
							Leg(
								b.TermAs[C](
									"module_sum(P.add, "+
										"    P.zero, "+
										"    fun_support(N.zero, u) ∪ fun_support(N.zero, v), "+
										"    λx:D. T(x, fun_add(u, v, x)))"),
								"the sum for u + v runs over the union",
								By(sumOver.At(b.TermAs[Fun[D, B]]("fun_add(u, v)"), union), finite, inside, sumValues, sumOff)),
							Leg(
								b.TermAs[C](
									"module_sum(P.add, "+
										"    P.zero, "+
										"    fun_support(N.zero, u) ∪ fun_support(N.zero, v), "+
										"    λx:D. T(x, u(x)) + T(x, v(x)))"),
								"each term splits",
								By(module.ModuleSumCongruence, splits)),
							FinalLeg(
								"the sum splits into the sums of the two parts, which are the sums for u and v",
								sumU.Rw(),
								sumV.Rw(),
								By(
									module.ModuleSumAdd.Read(moduleP).At(
										union, b.TermAs[Fun[D, C]]("λx:D. T(x, u(x))"), b.TermAs[Fun[D, C]]("λx:D. T(x, v(x))")),
									finite,
									terms)),
						))
				}))

			homogeneous := a.Have(
				"the map commutes with scaling: c passes into each term and out of the sum",
				Statement{
					Binders: "∀c:A. ∀u:(D → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ finite_supp(N.zero, N.carrier, S)",
					},
					Conclusion: "module_sum(P.add, " +
						"    P.zero, " +
						"    fun_support(N.zero, λx:D. fun_smul(N.smul, c, u, x)), " +
						"    λx:D. T(x, fun_smul(N.smul, c, u, x))) = " +
						"c • module_sum(P.add, P.zero, fun_support(N.zero, u), λx:D. T(x, u(x)))",
				},
				Derive(func(b *Argument) {
					scale := b.FixAs[A]("c")
					b.FixAs[Fun[D, B]]("u")
					assumed := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u is a finitely supported function on S")
					scalar := proof.MemberOf(scale, assumed[0])
					uParts := b.Conjuncts(
						b.Simplified(assumed[1], Fwd(FiniteSuppMember)),
						"the support of u is finite",
						"and lies in S",
						"u takes its values in N")
					support := b.TermAs[Set[D]]("fun_support(N.zero, u)")
					scaledValues := b.Have(
						"c • u takes its values in N",
						"∀x:D. fun_smul(N.smul, c, u, x) ∈ N.carrier",
						Simp(Fwd(FunSmulDef)),
						By(scalar, uParts[2], module.SmulIn.Read(moduleN)))
					scaledOff := b.Have(
						"and vanishes off the support of u, c • N.zero being N.zero",
						"∀x:D. x ∉ fun_support(N.zero, u) ⇒ fun_smul(N.smul, c, u, x) = N.zero",
						Derive(func(e *Argument) {
							e.FixAs[D]("x")
							outside := e.Assume()
							zero := e.Have(
								"u vanishes at x",
								"u(x) = N.zero",
								BySets(outside))
							e.Show(
								"the value c • u(x) is c • N.zero",
								Simp(Fwd(FunSmulDef)),
								zero.Rw(),
								By(scalar, module.SmulZero.Read(moduleN)))
						}))
					regroup := b.Have(
						"each term T(x, c • u(x)) is c • T(x, u(x)), T(x) commuting with scaling",
						"∀x:D. x ∈ fun_support(N.zero, u) ⇒ T(x, fun_smul(N.smul, c, u, x)) = c • T(x, u(x))",
						Simp(Fwd(FunSmulDef)),
						By(scalings, scalar, uParts[1], uParts[2], set_basic.SubsetDef))
					terms := b.Have(
						"each T(x, u(x)) over the support lies in P",
						"∀x:D. x ∈ fun_support(N.zero, u) ⇒ T(x, u(x)) ∈ P.carrier",
						By(images, uParts[1], uParts[2], set_basic.SubsetDef))
					b.Show(
						"the sum for c • u is c times the sum for u",
						CalcEq(
							Leg(
								b.TermAs[C](
									"module_sum(P.add, P.zero, fun_support(N.zero, u), λx:D. T(x, fun_smul(N.smul, c, u, x)))"),
								"the sum for c • u runs over the support of u",
								By(
									sumOver.At(b.TermAs[Fun[D, B]]("fun_smul(N.smul, c, u)"), support),
									uParts[0],
									uParts[1],
									scaledValues,
									scaledOff)),
							Leg(
								b.TermAs[C]("module_sum(P.add, P.zero, fun_support(N.zero, u), λx:D. c • T(x, u(x)))"),
								"c passes into each term",
								By(module.ModuleSumCongruence, regroup)),
							FinalLeg(
								"and out of the sum",
								By(
									module.ModuleSumSmul.Read(moduleP).At(support, scalar, b.TermAs[Fun[D, C]]("λx:D. T(x, u(x))")),
									uParts[0],
									terms)),
						))
				}))

			a.Show(
				"so the map is a homomorphism of the finitely supported functions on S, a module over R, into P",
				By(
					FiniteSuppModuleOn.Read(moduleN),
					moduleP,
					inP,
					additiveMap,
					homogeneous,
					module_homomorphism.ModuleHomomorphismDef))
		}),
})}
