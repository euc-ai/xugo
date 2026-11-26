// hom_module.go — the module of homomorphisms between two modules on
// sets: the homomorphisms M → N, read as zero off M so that they form a
// set of functions closed under the pointwise operations, which make
// it a module over the same ring. Composing after a homomorphism
// N → L is a homomorphism of these modules, one-to-one when the
// homomorphism is, and exact in the middle of a left-exact sequence:
// Hom(M, −) is left exact. The maps of a commutative ring R, a module
// over itself, into a module W are the multiplications x ↦ x · v by the
// vectors v of W, each determined by its value at one: Hom(R, W) is W.
// For a ring map f from R to T, a module over T read over R through f,
// r acting as f(r), is a module over R — the restriction of scalars; the
// R-linear maps from T to a module M over R are a module over T, T acting
// on the argument — the coextension of M — and the T-linear maps of a
// module over T into it are the R-linear maps into M.

package hom_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// HomSetDef — `hom_set(R, M, N)`: the homomorphisms M → N that are
// zero off M.
var HomSetDef = homSetDefThm{family.Define(registry.DefEntry{
	Name:  "HomSetDef",
	Const: "hom_set",
	Type:  "ring_ops(A) → module_ops(A, B) → module_ops(A, C) → set(B → C)",
	Key:   "prop_b9f093255ac1536",

	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    hom_set(R, M, N) = " +
			"    {f:(B → C) | module_homomorphism(R, M, N, f) ∧ (∀u:B. u ∉ M.carrier ⇒ f(u) = N.zero)}",
	},
})}

// InHomSet — a map lies in hom_set(R, M, N) exactly when it is a
// homomorphism of M into N that is zero off M: the set-builder of
// HomSetDef, read at one map.
var InHomSet = inHomSetThm{family.Add(registry.ProofEntry{
	Name: "InHomSet",
	Key:  "prop_1344fadcebc0b9e",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀g:(B → C). "+
		"    g ∈ hom_set(R, M, N) ⇔ "+
		"    module_homomorphism(R, M, N, g) ∧ (∀u:B. u ∉ M.carrier ⇒ g(u) = N.zero)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			g *Arrow[B, C],
		) {
			a.Show(
				"hom_set gathers the homomorphisms that are zero off M",
				Simp(Fwd(HomSetDef)),
				BySets())
		}),
})}

// HomModuleDef — `hom_module(R, M, N)`: the homomorphisms M → N that are
// zero off M, under the pointwise operations of N.
var HomModuleDef = homModuleDefThm{family.Define(registry.DefEntry{
	Name: "HomModuleDef", Const: "hom_module",
	Key:  "prop_e51b04fb53b29e9",
	Type: "ring_ops(A) → module_ops(A, B) → module_ops(A, C) → module_ops(A, B → C)",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    hom_module(R, M, N) = " +
			"    mk_module(fun_add⟨D:B⟩(N.add), " +
			"        fun_zero⟨D:B⟩(N.zero), " +
			"        fun_neg⟨D:B⟩(N.neg), " +
			"        fun_smul⟨D:B⟩(N.smul), " +
			"        hom_set(R, M, N))",
	},
	Deps: []registry.EntryLike{HomSetDef},
})}

// HomSetModuleOn — the homomorphisms form a module under the pointwise
// operations: they are a submodule of the module of all functions into N
// that vanish off M. A homomorphism vanishing off M is such a function,
// its values lying in N; the function module's operations keep a function
// in it, and they keep a homomorphism one, each law of the zero map, of
// f + g, of −f and of c • f being a computation in N at the values of f
// and g — c • f commutes with scaling since the scalars commute.
var HomSetModuleOn = homSetModuleOnThm{family.Add(registry.ProofEntry{
	Name: "HomSetModuleOn",
	Key:  "prop_4d3d39a8ce2e33f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_on(R, hom_module(R, M, N))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			modules Fact,
		) {
			parts := a.Conjuncts(
				modules,
				"M is a module over R",
				"and so is N")
			moduleM, moduleN := parts[0], parts[1]

			functionModule := a.Have(
				"the functions into N vanishing off M are a module over R",
				"module_on(R, function_module(N, M.carrier))",
				By(function_module.FunModuleOn.Read(moduleN)))
			pointwise := module.AddGroupOn.Read(functionModule)
			member := a.Have(
				"a member of hom_set is a homomorphism among those "+
					"functions: on M its values lie in N, and off M they are zero",
				"∀f:(B → C). "+
					"    f ∈ hom_set(R, M, N) ⇔ "+
					"    f ∈ fun_module(N.zero, N.carrier, M.carrier) ∧ module_homomorphism(R, M, N, f)",
				Simp(Fwd(InHomSet), Fwd(function_module.FunModuleDef)),
				BySets(module_homomorphism.HomIn, group.OneIn.Read(module.AddGroupOn.Read(moduleN))))

			zeroHom := a.Have(
				"the zero map is a homomorphism",
				"module_homomorphism(R, M, N, fun_zero(N.zero))",
				Simp(Fwd(module_homomorphism.ModuleHomomorphismDef), Fwd(function_module.FunZeroDef)),
				ByChase(Depth(0), moduleM, moduleN))
			zeroIn := a.Have(
				"so it is a member, the zero of the function module",
				"fun_zero(N.zero) ∈ hom_set(R, M, N)",
				By(member.At(a.TermAs[Fun[B, C]]("fun_zero(N.zero)")), group.OneIn.Read(pointwise), zeroHom))
			addIn := a.Have(
				"a sum of members is a member",
				Statement{
					Binders: "∀f g:(B → C).",
					Hypotheses: []string{
						"f ∈ hom_set(R, M, N)",
						"g ∈ hom_set(R, M, N)",
					},
					Conclusion: "fun_add(N.add, f, g) ∈ hom_set(R, M, N)",
				},
				Derive(func(b *Argument) {
					f, g := b.FixAs[Fun[B, C]](), b.FixAs[Fun[B, C]]()
					members := b.Assume()
					homs := b.Have(
						"f and g are homomorphisms",
						"module_homomorphism(R, M, N, f) ∧ module_homomorphism(R, M, N, g)",
						By(member.At(f), member.At(g), members))
					sumHom := b.Have(
						"so is f + g: at u it is f(u) + g(u)",
						"module_homomorphism(R, M, N, fun_add(N.add, f, g))",
						Simp(Fwd(module_homomorphism.ModuleHomomorphismDef), Fwd(function_module.FunAddDef)),
						ByChase(Depth(0), moduleM, moduleN, homs))
					b.Show(
						"so f + g is a member: the function module is closed under the sum",
						By(
							member.At(b.TermAs[Fun[B, C]]("fun_add(N.add, f, g)")),
							member.At(f),
							member.At(g),
							members,
							group.MulIn.Read(pointwise).AsFact().At(f, g),
							sumHom))
				}))
			negIn := a.Have(
				"a negation of a member is a member",
				"∀f:(B → C). f ∈ hom_set(R, M, N) ⇒ fun_neg(N.neg, f) ∈ hom_set(R, M, N)",
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[B, C]]()
					fIn := b.Assume()
					fHom := b.Have(
						"f is a homomorphism",
						"module_homomorphism(R, M, N, f)",
						By(member.At(f), fIn))
					negHom := b.Have(
						"so is -f: at u it is -f(u)",
						"module_homomorphism(R, M, N, fun_neg(N.neg, f))",
						By(module_homomorphism.HomPointwiseNeg.Read(fHom), function_module.FunNegDef))
					b.Show(
						"so -f is a member: the function module is closed under the negation",
						By(
							member.At(b.TermAs[Fun[B, C]]("fun_neg(N.neg, f)")),
							member.At(f),
							fIn,
							group.InvIn.Read(pointwise).AsFact().At(f),
							negHom))
				}))
			smulIn := a.Have(
				"a scaled member is a member",
				Statement{
					Binders: "∀c:A. ∀f:(B → C).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"f ∈ hom_set(R, M, N)",
					},
					Conclusion: "fun_smul(N.smul, c, f) ∈ hom_set(R, M, N)",
				},
				Derive(func(b *Argument) {
					c, f := b.FixAs[A](), b.FixAs[Fun[B, C]]()
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"f is a member")
					scalar, fIn := given[0], given[1]
					fHom := b.Have(
						"f is a homomorphism",
						"module_homomorphism(R, M, N, f)",
						By(member.At(f), fIn))
					scaledHom := b.Have(
						"so is c • f: at u it is c • f(u), and the scalars commute",
						"module_homomorphism(R, M, N, fun_smul(N.smul, c, f))",
						Simp(Fwd(module_homomorphism.ModuleHomomorphismDef), Fwd(function_module.FunSmulDef)),
						ByChase(Depth(0), moduleM, moduleN, scalar, fHom))
					b.Show(
						"so c • f is a member: the function module is closed under scaling",
						By(
							member.At(b.TermAs[Fun[B, C]]("fun_smul(N.smul, c, f)")),
							member.At(f),
							scalar,
							fIn,
							module.SmulIn.Read(functionModule).AsFact().At(c, f),
							scaledHom))
				}))

			inFunctions := a.Have(
				"every member lies in the function module",
				"∀f:(B → C). f ∈ hom_set(R, M, N) ⇒ f ∈ fun_module(N.zero, N.carrier, M.carrier)",
				a.ForEach(func(f *Expr[Fun[B, C]]) Action { return By(member.At(f)) }))
			subgroup := a.Have(
				"the members are a subgroup of the function module under the pointwise addition",
				"subgroup(mk_group(fun_add(N.add), "+
					"        fun_zero(N.zero), "+
					"        fun_neg(N.neg), "+
					"        fun_module(N.zero, N.carrier, M.carrier)), "+
					"    hom_set(R, M, N))",
				By(inFunctions, zeroIn, addIn, negIn, group.SubgroupDef, set_basic.SubsetDef))
			isSubmodule := a.Have(
				"closed under scaling, a submodule of it",
				"submodule(R, function_module(N, M.carrier), hom_set(R, M, N))",
				Simp(
					Fwd(submodule.SubmoduleDef),
					Fwd(module_record.ModuleAdditiveGroupDef),
					Fwd(function_module.FunctionModuleDef),
					Fwd(module_record.ModAddDef),
					Fwd(module_record.ModZeroDef),
					Fwd(module_record.ModNegDef),
					Fwd(module_record.ModSmulDef),
					Fwd(module_record.ModCarrierDef)),
				Derive(func(b *Argument) {
					u, c := b.FixAs[Fun[B, C]](), b.FixAs[A]()
					b.Show(
						"the additive subgroup and the scalar closure give the submodule conditions",
						By(subgroup, smulIn.At(c, u)))
				}))
			restricted := a.Have(
				"hom_module(R, M, N) is the function module restricted to hom_set: the same pointwise operations",
				"hom_module(R, M, N) = restrict_module(function_module(N, M.carrier), hom_set(R, M, N))",
				Simp(
					Fwd(HomModuleDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(function_module.FunctionModuleDef)),
				Refl())
			a.Show(
				"a submodule is a module on its own",
				restricted.Rw(),
				By(submodule.SubmoduleModuleOn.Read(functionModule), isSubmodule))
		}),
})}

// PostComposeHom — composing after a homomorphism g: N → L is a
// homomorphism Hom(M, N) → Hom(M, L). Both are modules over R, and a
// member f of Hom(M, N) takes its values in N: on M it maps into N, and
// off M its value is N.zero. So g ∘ f is a homomorphism of M into L that
// is zero off M, g carrying N.zero to L.zero; and at each point g carries
// f(u) + h(u) and c • f(u) to the sum and the scaling of its values, the
// pointwise operations of Hom(M, L).
var PostComposeHom = postComposeHomThm{family.Add(registry.ProofEntry{
	Name: "PostComposeHom",
	Key:  "prop_6af221f151a0c807",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_homomorphism(R, N, L, g)",
		},
		Conclusion: "module_homomorphism(R, hom_module(R, M, N), hom_module(R, M, L), λf:(B → C). g ∘ f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			g *Arrow[C, D],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a module over R",
				"g is a homomorphism of N into L")
			moduleM, linear := parts[0], parts[1]
			moduleN, moduleL :=
				module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
			source := a.Have(
				"Hom(M, N) is a module over R",
				"module_on(R, hom_module(R, M, N))",
				By(HomSetModuleOn.At(R, M, N), moduleM, moduleN))
			target := a.Have(
				"and so is Hom(M, L)",
				"module_on(R, hom_module(R, M, L))",
				By(HomSetModuleOn.At(R, M, L), moduleM, moduleL))

			values := a.Have(
				"a member of Hom(M, N) takes its values in N: on M it maps into N, and off M its value is N.zero",
				"∀f:(B → C). ∀u:B. f ∈ hom_set(R, M, N) ⇒ f(u) ∈ N.carrier",
				Derive(func(b *Argument) {
					f, u := b.FixAs[Fun[B, C]](), b.FixAs[B]()
					fIn := b.Assume()
					member := InHomSet.At(R, M, N, f)
					b.Cases(b.Term("u ∈ M.carrier"))
					b.When(
						"on M, f is a homomorphism into N",
						func(c *Argument, uIn Fact) {
							c.Show(
								"f carries u into N",
								By(member, fIn, uIn, module_homomorphism.HomIn.At(R, M, N, f, u)))
						})
					b.Otherwise(
						"off M, f(u) is N.zero, a vector of N",
						func(c *Argument, uOut Fact) {
							zero := c.Have(
								"f vanishes at u",
								"f(u) = N.zero",
								By(member, fIn, uOut))
							c.Show(
								"N.zero lies in N",
								zero.Rw(),
								Cite(group.OneIn.Read(module.AddGroupOn.Read(moduleN))))
						})
				}))
			lands := a.Have(
				"composing after g keeps a member: g ∘ f is a homomorphism of M into L, zero off M",
				"∀f:(B → C). f ∈ hom_set(R, M, N) ⇒ g ∘ f ∈ hom_set(R, M, L)",
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[B, C]]()
					fIn := b.Assume()
					fParts := b.Conjuncts(
						b.Have(
							"f is a homomorphism of M into N that vanishes off M",
							"module_homomorphism(R, M, N, f) ∧ (∀u:B. u ∉ M.carrier ⇒ f(u) = N.zero)",
							By(InHomSet.At(R, M, N, f), fIn)),
						"f is a homomorphism of M into N",
						"f vanishes off M")
					fHom, fZero := fParts[0], fParts[1]
					composite := b.Have(
						"g ∘ f is a homomorphism of M into L, the composite of two homomorphisms",
						"module_homomorphism(R, M, L, g ∘ f)",
						By(module_homomorphism.HomCompose.At(R, M, N, L, f, g), fHom, linear))
					vanishes := b.Have(
						"off M, g ∘ f takes the value g(N.zero), which is L.zero",
						"∀u:B. u ∉ M.carrier ⇒ (g ∘ f)(u) = L.zero",
						Derive(func(c *Argument) {
							u := c.FixAs[B]()
							uOutside := c.Assume()
							c.Show(
								"g carries N.zero to L.zero",
								Simp(Fwd(functions.ComposeApply)),
								GroupPremises(uOutside, fZero.At(u)).Rw(),
								Cite(module_homomorphism.HomZero.Read(linear)))
						}))
					b.Show(
						"so g ∘ f is a member of Hom(M, L)",
						By(InHomSet.At(R, M, L, b.TermAs[Fun[B, D]]("g ∘ f")), composite, vanishes))
				}))
			adds := a.Have(
				"composing after g carries the pointwise sum of members to the pointwise sum of the composites",
				Statement{
					Binders: "∀f h:(B → C).",
					Hypotheses: []string{
						"f ∈ hom_set(R, M, N)",
						"h ∈ hom_set(R, M, N)",
					},
					Conclusion: "g ∘ fun_add(N.add, f, h) = fun_add(L.add, g ∘ f, g ∘ h)",
				},
				Derive(func(b *Argument) {
					f, h := b.FixAs[Fun[B, C]](), b.FixAs[Fun[B, C]]()
					members := b.Assume()
					b.Do(Funext(), Simp(Fwd(functions.ComposeApply), Fwd(function_module.FunAddDef)))
					u := b.FixAs[B]("u")
					b.Show(
						"g(f(u) + h(u)) is g(f(u)) + g(h(u)), f(u) and h(u) lying in N",
						By(
							members,
							values.At(f, u),
							values.At(h, u),
							module_homomorphism.HomAdd.Read(linear).AsFact().At(b.TermAs[C]("f(u)"), b.TermAs[C]("h(u)"))))
				}))
			scales := a.Have(
				"composing after g carries the pointwise scaling of "+
					"a member to the pointwise scaling of the composite",
				Statement{
					Binders: "∀c:A. ∀f:(B → C).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"f ∈ hom_set(R, M, N)",
					},
					Conclusion: "g ∘ fun_smul(N.smul, c, f) = fun_smul(L.smul, c, g ∘ f)",
				},
				Derive(func(b *Argument) {
					c, f := b.FixAs[A](), b.FixAs[Fun[B, C]]()
					hypotheses := b.Assume()
					b.Do(Funext(), Simp(Fwd(functions.ComposeApply), Fwd(function_module.FunSmulDef)))
					u := b.FixAs[B]("u")
					b.Show(
						"g(c • f(u)) is c • g(f(u)), f(u) lying in N",
						By(
							hypotheses,
							values.At(f, u),
							module_homomorphism.HomSmul.Read(linear).AsFact().At(c, b.TermAs[C]("f(u)"))))
				}))
			a.Show(
				"spelled out at the two modules of homomorphisms, each condition of a homomorphism is a fact above",
				Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(source, target, lands, adds, scales))
		}),
})}

// PostComposeInjective — composing after a map one-to-one on N is
// one-to-one on the homomorphisms M → N: two homomorphisms with one
// composite agree on M, where their values lie in N and g separates them,
// and off M both are zero.
var PostComposeInjective = postComposeInjectiveThm{family.Add(registry.ProofEntry{
	Name: "PostComposeInjective",
	Key:  "prop_7d8615e68bc506da",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀g:(C → D). ∀f h:(B → C).",
		Hypotheses: []string{
			"injective_on(N.carrier, g)",
			"f ∈ hom_set(R, M, N)",
			"h ∈ hom_set(R, M, N)",
			"g ∘ f = g ∘ h",
		},
		Conclusion: "f = h",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			g *Arrow[C, D],
			f, h *Arrow[B, C],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"g is one-to-one on N",
				"f is a homomorphism of M into N, zero off M",
				"so is h",
				"g ∘ f = g ∘ h")
			oneToOne, fIn, hIn, composites := parts[0], parts[1], parts[2], parts[3]
			fMember := a.Conjuncts(
				a.Simplified(fIn, Fwd(InHomSet)),
				"f is a homomorphism of M into N",
				"f vanishes off M")
			hMember := a.Conjuncts(
				a.Simplified(hIn, Fwd(InHomSet)),
				"h is a homomorphism of M into N",
				"h vanishes off M")
			separates := a.Unfolded(oneToOne, functions.InjectiveOnDef)
			a.Do(Funext())
			u := a.FixAs[B]("u")
			a.Cases(a.Term("u ∈ M.carrier"))
			a.When(
				"on M, f(u) and h(u) lie in N, and g takes them to one value",
				func(b *Argument, uIn Fact) {
					um := proof.MemberOf(u, uIn)
					atU := b.Have(
						"g ∘ f and g ∘ h agree at u",
						"(g ∘ f)(u) = (g ∘ h)(u)",
						composites.Rw(),
						Basic())
					b.Show(
						"g separates f(u) and h(u), two points of N",
						By(
							separates.At(f.Apply(u), h.Apply(u)),
							b.Simplified(atU, Fwd(functions.ComposeApply)),
							module_homomorphism.HomIn.Read(fMember[0]).At(um),
							module_homomorphism.HomIn.Read(hMember[0]).At(um)))
				})
			a.Otherwise(
				"off M, f(u) and h(u) are both N.zero",
				func(b *Argument, uOut Fact) {
					b.Show(
						"f(u) = N.zero = h(u)",
						CalcEq(
							Leg(
								b.TermAs[C]("N.zero"),
								"f vanishes off M",
								By(fMember[1].At(u), uOut)),
							FinalLeg(
								"and so does h",
								By(hMember[1].At(u), uOut)),
						))
				})
		}),
})}

// HomLeftExact — Hom(M, −) is exact in the middle of a left-exact
// sequence: for i: N → L linear and one-to-one with image the kernel of
// a map p: L → K that keeps zero, the homomorphisms M → L that p kills
// are those through i. A homomorphism h that p kills takes M into the
// kernel of p, the image of i, and so lifts through the inverse of i on
// that image.
var HomLeftExact = homLeftExactThm{family.Add(registry.ProofEntry{
	Name: "HomLeftExact",
	Key:  "prop_ea5ab2f016974682",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀K:module_ops(A, E). " +
			"∀i:(C → D). " +
			"∀p:(D → E).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_homomorphism(R, N, L, i)",
			"p(L.zero) = K.zero",
			"injective_on(N.carrier, i)",
			"exact_at(K.zero, N.carrier, L.carrier, i, p)",
		},
		Conclusion: "exact_at(fun_zero⟨D:B⟩(K.zero), " +
			"    hom_set(R, M, N), " +
			"    hom_set(R, M, L), " +
			"    λf:(B → C). i ∘ f, " +
			"    λf:(B → D). p ∘ f)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]], K *Expr[ModuleOps[A, E]], i *Arrow[C, D], p *Arrow[D, E],
			source module.ModuleFact[on.R, on.M], iLinear, pZero, oneToOne, exact Fact) {
			kZero := a.TermAs[E]("K.zero")
			nCarrier, lCarrier := a.TermAs[Set[C]]("N.carrier"), a.TermAs[Set[D]]("L.carrier")
			// Exactness is an equation of two sets of maps, the image of i ∘ − and the
			// kernel of p ∘ −; equal sets have the same members, so each h is in both or neither.
			a.Do(Simp(Fwd(module_homomorphism.ExactAtDef)), Simp(Fwd(set_basic.Extension)))
			h := a.FixAs[Fun[B, D]]("h")
			a.Iff()
			a.Backward(
				"a homomorphism killed by p lifts through the inverse of i onto its image",
				func(b *Argument, killed Fact) {
					kernel := b.Have(
						"h is normalized and p kills it",
						"h ∈ hom_set(R, M, L) ∧ p ∘ h = fun_zero(K.zero)",
						BySets(killed, group_homomorphism.InKernel))
					hLinear := b.Have(
						"h is linear",
						"module_homomorphism(R, M, L, h)",
						BySets(kernel, InHomSet.At(R, M, L, h)))
					I, imageDef := b.LetAs[Set[D]]("I", "image(i, N.carrier)")
					restricted := b.TermAs[ModuleOps[A, D]]("restrict_module(L, I)")
					inverse := b.TermAs[Fun[D, C]]("inverse_on(N.carrier, i)")
					ontoImage := b.Have(
						"i identifies N with its image in L",
						"module_isomorphism(R, N, restrict_module(L, I), i)",
						By(
							Normalized,
							imageDef,
							oneToOne,
							iLinear,
							module_homomorphism.IsomorphismOntoImage.At(R, N, L, i)))
					valuesInImage := b.Have(
						"h takes every point of M into the image of i",
						"∀x:B. x ∈ M.carrier ⇒ h(x) ∈ I",
						Derive(func(c *Argument) {
							x := c.FixAs[B]("x")
							xIn := c.Assume()
							valueInKernel := c.Have(
								"h(x) lies in L and is killed by p",
								"h(x) ∈ L.carrier ∧ p(h(x)) = K.zero",
								By(
									xIn,
									kernel,
									module_homomorphism.HomIn.Read(hLinear).At(proof.MemberOf(x, xIn)),
									functions.ComposeApply.At(p, h),
									function_module.FunZeroDef.At(kZero, x)))
							c.Show(
								"exactness places h(x) in I",
								BySets(
									imageDef,
									valueInKernel,
									exact,
									module_homomorphism.ExactAtDef.At(
										kZero, nCarrier, lCarrier, i, p),
									group_homomorphism.InKernel.At(
										kZero, lCarrier, p, c.TermAs[D]("h(x)"))))
						}))
					corestricted := b.Have(
						"h is linear into the image submodule",
						"module_homomorphism(R, M, restrict_module(L, I), h)",
						By(
							module_homomorphism.ImageSubmodule.Read(iLinear),
							valuesInImage,
							imageDef,
							hLinear,
							module_homomorphism.HomCorestrict.At(R, M, L, h, I)))
					inverseLinear := b.Have(
						"the inverse on the image is linear",
						"module_homomorphism(R, restrict_module(L, I), N, inverse_on(N.carrier, i))",
						By(
							ontoImage,
							module_homomorphism.IsomorphismInverse.At(R, N, restricted, i),
							module_homomorphism.ModuleIsomorphismDef.At(R, restricted, N, inverse)))
					q, qDef := b.LetAs[Fun[B, C]]("q", "inverse_on(N.carrier, i) ∘ h")
					qLinear := b.Have(
						"pulling h back along i gives a linear map into N",
						"module_homomorphism(R, M, N, q)",
						By(
							Normalized,
							qDef,
							corestricted,
							inverseLinear,
							module_homomorphism.HomCompose.At(R, M, restricted, N, h, inverse)))
					qZero := b.Have(
						"the pullback is zero off M because the inverse preserves zero",
						"∀x:B. x ∉ M.carrier ⇒ q(x) = N.zero",
						By(
							module_homomorphism.HomZero.Read(inverseLinear),
							qDef,
							kernel,
							InHomSet.At(R, M, L, h),
							functions.ComposeApply.At(inverse, h)))
					recovers := b.Have(
						"composing the pullback with i recovers h everywhere",
						"i ∘ q = h",
						Derive(func(c *Argument) {
							c.Do(Funext())
							x := c.FixAs[B]("x")
							c.Cases(c.TermAs[Bool]("x ∈ M.carrier"))
							c.When(
								"on M the inverse recovers the point h(x) of the image",
								func(d *Argument, xIn Fact) {
									d.Show(
										"i(q(x)) = h(x)",
										By(
											Normalized,
											valuesInImage.At(x),
											qDef,
											imageDef,
											xIn,
											functions.InverseOnRight.At(nCarrier, i, d.TermAs[D]("h(x)")),
											functions.ComposeApply.At(i, q),
											functions.ComposeApply.At(inverse, h)))
								})
							c.Otherwise(
								"off M both h and i composed with q vanish",
								func(d *Argument, xOut Fact) {
									d.Show(
										"i sends q(x) = N.zero to h(x) = L.zero",
										By(
											module_homomorphism.HomZero.Read(iLinear),
											xOut,
											qZero.At(x),
											kernel,
											InHomSet.At(R, M, L, h),
											functions.ComposeApply.At(i, q)))
								})
						}))
					b.Show(
						"the normalized pullback q witnesses membership in the postcomposition image",
						BySets(qZero, recovers, qLinear, InHomSet.At(R, M, N, q)))
				})
			a.Forward(
				"postcomposition through i is killed by p",
				func(b *Argument, inImage Fact) {
					j, factors := b.ObtainAs[Fun[B, C]](
						"choose a normalized factor j of h through i",
						"∃j:(B → C). j ∈ hom_set(R, M, N) ∧ h = i ∘ j",
						BySets(inImage),
						Named("j"))
					postLinear := b.Have(
						"postcomposing by i is linear on homomorphism modules",
						"module_homomorphism(R, hom_module(R, M, N), hom_module(R, M, L), λf:(B → C). i ∘ f)",
						By(source, iLinear, PostComposeHom.At(R, M, N, L, i)))
					hIn := b.Have(
						"the composite h is normalized",
						"h ∈ hom_set(R, M, L)",
						By(Normalized, factors, module_homomorphism.HomIn.Read(postLinear).AsFact().At(j)))
					jLinear := b.Have(
						"the factor j is linear",
						"module_homomorphism(R, M, N, j)",
						BySets(factors, InHomSet.At(R, M, N, j)))
					killed := b.Have(
						"p kills h on M and off M",
						"p ∘ h = fun_zero(K.zero)",
						Derive(func(c *Argument) {
							c.Do(Funext())
							x := c.FixAs[B]("x")
							c.Cases(c.TermAs[Bool]("x ∈ M.carrier"))
							c.When(
								"on M exactness kills i(j(x))",
								func(d *Argument, xIn Fact) {
									d.Show(
										"p(h(x)) = K.zero",
										By(
											Normalized,
											xIn,
											factors,
											exact,
											module_homomorphism.HomIn.Read(jLinear).At(proof.MemberOf(x, xIn)),
											module_homomorphism.ExactComposeZero.At(
												kZero, nCarrier, lCarrier, i, p, d.TermAs[C]("j(x)")),
											functions.ComposeApply.At(p, h),
											functions.ComposeApply.At(i, j),
											function_module.FunZeroDef.At(kZero, x)))
								})
							c.Otherwise(
								"off M the normalization of h and preservation of zero suffice",
								func(d *Argument, xOut Fact) {
									d.Show(
										"p(h(x)) = p(L.zero) = K.zero",
										By(
											pZero,
											xOut,
											hIn,
											InHomSet.At(R, M, L, h),
											functions.ComposeApply.At(p, h),
											function_module.FunZeroDef.At(kZero, x)))
								})
						}))
					b.Show(
						"h belongs to the kernel of postcomposition by p",
						BySets(
							killed,
							hIn,
							group_homomorphism.InKernel.At(
								b.TermAs[Fun[B, E]]("fun_zero(K.zero)"), b.TermAs[Set[Fun[B, D]]]("hom_set(R, M, L)"),
								b.TermAs[Fun2[Fun[B, D], B, E]]("λf:(B → D). p ∘ f"), h)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The maps out of the ring: Hom(R, W) is W by evaluation at one
// ---------------------------------------------------------------------------

// RegularHomIsScalarMap — every map of the regular module R into W, zero
// off R, is multiplication by its value at one: on R, x is x · one and the
// map is R-linear, and off R both sides are the zero of W.
var RegularHomIsScalarMap = regularHomIsScalarMapThm{family.Add(registry.ProofEntry{
	Name: "RegularHomIsScalarMap",
	Key:  "prop_1927825a47413c27",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀W:module_ops(A, B). ∀ψ:(A → B). ∀x:A.",
		Hypotheses: []string{"ψ ∈ hom_set(R, regular_module(R), W)"},
		Conclusion: "ψ(x) = COND(x ∈ R.carrier, W.smul(x, ψ(R.one)), W.zero)",
	},
		func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			W *Expr[ModuleOps[A, B]],
			ψ *Arrow[A, B],
			x *Expr[A],
			normalized Fact,
		) {
			expanded := a.Unfolded(normalized, HomSetDef)
			linear := a.Have(
				"the normalized map is linear on the regular module",
				"module_homomorphism(R, regular_module(R), W, ψ)",
				By(expanded))
			a.Cases(a.TermAs[Bool]("x ∈ R.carrier"))
			a.When(
				"linearity at x times one determines the map on the carrier",
				func(b *Argument, xIn Fact) {
					b.Show(
						"ψ(x) = x · ψ(one), since x = x · one and ψ is linear",
						By(
							Normalized,
							comm_ring.OneIn.Read(R),
							xIn,
							comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(R)).AsFact().At(x),
							module_homomorphism.HomSmul.Read(linear).AsFact().At(x, b.TermAs[A]("R.one"))))
				})
			a.Otherwise(
				"the normalized map vanishes off the carrier",
				func(b *Argument, xOut Fact) {
					b.Show(
						"the zero extension determines the remaining values",
						BySets(xOut, expanded))
				})
		}),
})}

// ScalarMapIsRegularHom — for a vector v of a module W over R,
// multiplication x ↦ x · v on R, zero off R, is a map of the regular
// module into W: each condition of a homomorphism is a module law of W
// read at v.
var ScalarMapIsRegularHom = scalarMapIsRegularHomThm{family.Add(registry.ProofEntry{
	Name: "ScalarMapIsRegularHom",
	Key:  "prop_3ec29221a12c5b0",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀W:module_ops(A, B). ∀v:B.",
		Hypotheses: []string{"module_on(R, W)", "v ∈ W.carrier"},
		Conclusion: "(λx:A. COND(x ∈ R.carrier, W.smul(x, v), W.zero)) ∈ hom_set(R, regular_module(R), W)",
	},
		func(a *Argument, R comm_ring.CommRingFact[on.R], W *Expr[ModuleOps[A, B]], v *Expr[B], h Fact) {
			parts := a.Conjuncts(
				h,
				"W is a module over R",
				"v lies in W")
			linear := a.Have(
				"the normalized scalar map is linear",
				"module_homomorphism(R, regular_module(R), W, λx:A. COND(x ∈ R.carrier, W.smul(x, v), W.zero))",
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				SplitConjAll(
					Case(
						"the source, the regular module, is a module over R",
						By(module.RegularModuleOn.Read(R))),
					Case(
						"the target W is a module over R",
						By(parts[0])),
					Case(
						"the map carries R into W: u · v lies in W for u in R",
						Derive(func(b *Argument) {
							u := b.FixAs[A]("u")
							uIn := b.Assume()
							b.Show(
								"scalar multiplication preserves the carrier",
								By(uIn, parts[1], module.SmulIn.Read(parts[0]).AsFact().At(u, v)))
						})),
					Case(
						"the map preserves addition: (u + w) · v = u · v + w · v",
						Derive(func(b *Argument) {
							u, w := b.FixAs[A]("u"), b.FixAs[A]("w")
							inputs := b.Assume()
							b.Show(
								"addition of scalars distributes over v",
								By(
									parts[1],
									inputs,
									comm_ring.AddIn.Read(R).AsFact().At(u, w),
									module.SmulAddRight.Read(parts[0]).AsFact().At(u, w, v)))
						})),
					Case(
						"the map preserves scalar multiplication: (c * u) · v = c · (u · v)",
						Derive(func(b *Argument) {
							c, u := b.FixAs[A]("c"), b.FixAs[A]("u")
							inputs := b.Assume()
							b.Show(
								"the action associates with scalar multiplication",
								By(
									parts[1],
									inputs,
									comm_ring.MulIn.Read(R).AsFact().At(c, u),
									module.SmulMul.Read(parts[0]).AsFact().At(c, u, v)))
						}))))
			a.Show(
				"the map is linear and zero off the regular module",
				BySets(
					linear,
					HomSetDef.At(a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, A]]("regular_module(R)"), W)))
		}),
})}

// ---------------------------------------------------------------------------
// Restriction and coextension of scalars
// ---------------------------------------------------------------------------

// algebraOverR is the ring T as a module over R through the ring map f:
// r acts by the product with f(r).
const algebraOverR = "scalar_restriction(f, regular_module(T))"

// RestrictScalarsModuleOn — restriction of scalars: a module over T, read
// over R through a ring map f from R to T, r acting as f(r), is a module
// over R. R is a ring, the source of f, and the vectors keep N's group and
// its commuting addition. Each law of the action is N's own at the scalars
// f(c) and f(d), which lie in T, carried back to c and d because f adds,
// multiplies and takes R.one to T.one.
var RestrictScalarsModuleOn = restrictScalarsModuleOnThm{family.Add(registry.ProofEntry{
	Name: "RestrictScalarsModuleOn",
	Key:  "prop_60dc709103c6bdf4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀f:(A → C). ∀N:module_ops(C, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"module_on(T, N)",
		},
		Conclusion: "module_on(R, scalar_restriction(f, N))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[C]],
			f *Arrow[A, C],
			N *Expr[ModuleOps[C, D]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a ring map from R to T",
				"N is a module over T")
			ringMap, nModule := parts[0], parts[1]
			into := ring_homomorphism.MapIn.Read(ringMap)

			// c in R acts on N as the scalar f(c) of T, so each law of the
			// action is N's law at f(c), read back through f.
			scaled := a.Have(
				"c • u lies in N: f(c) lies in T, and N is closed under scaling",
				"∀c:A. ∀u:D. c ∈ R.carrier ∧ u ∈ N.carrier ⇒ f(c) • u ∈ N.carrier",
				By(into, module.SmulIn.Read(nModule)))
			distributes := a.Have(
				"c • (u + v) = c • u + c • v: N's law at the scalar f(c)",
				Statement{
					Binders: "∀c:A. ∀u v:D.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ N.carrier",
						"v ∈ N.carrier",
					},
					Conclusion: "f(c) • (u + v) = f(c) • u + f(c) • v",
				},
				By(into, module.SmulAddLeft.Read(nModule)))
			sumOfScalars := a.Have(
				"(c + d) • u = c • u + d • u: f(c + d) = f(c) + f(d), and N's law at f(c) and f(d)",
				"∀c d:A. ∀u:D. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ N.carrier ⇒ f(c + d) • u = f(c) • u + f(d) • u",
				Derive(func(b *Argument) {
					c, d, u := b.FixAs[A](), b.FixAs[A](), b.FixAs[D]()
					members := b.Conjuncts(
						b.Assume(),
						"c is a scalar of R",
						"so is d",
						"u lies in N")
					cm, dm := proof.MemberOf(c, members[0]), proof.MemberOf(d, members[1])
					b.Show(
						"f(c + d) is f(c) + f(d), which acts on u as f(c) • u + f(d) • u",
						By(
							into,
							ring_homomorphism.MapAdd.Read(ringMap).At(cm, dm),
							module.SmulAddRight.Read(nModule).AsFact().At(f.Apply(c), f.Apply(d), u),
							members[2]))
				}))
			productOfScalars := a.Have(
				"(c * d) • u = c • (d • u): f(c * d) = f(c) * f(d), and N's law at f(c) and f(d)",
				"∀c d:A. ∀u:D. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ N.carrier ⇒ f(c * d) • u = f(c) • f(d) • u",
				Derive(func(b *Argument) {
					c, d, u := b.FixAs[A](), b.FixAs[A](), b.FixAs[D]()
					members := b.Conjuncts(
						b.Assume(),
						"c is a scalar of R",
						"so is d",
						"u lies in N")
					cm, dm := proof.MemberOf(c, members[0]), proof.MemberOf(d, members[1])
					b.Show(
						"f(c * d) is f(c) * f(d), which acts on u as f(c) • (f(d) • u)",
						By(
							into,
							ring_homomorphism.MapMul.Read(ringMap).At(cm, dm),
							module.SmulMul.Read(nModule).AsFact().At(f.Apply(c), f.Apply(d), u),
							members[2]))
				}))
			one := a.Have(
				"R.one • u = u: f(R.one) = T.one, which fixes every vector of N",
				"∀u:D. u ∈ N.carrier ⇒ f(R.one) • u = u",
				By(Normalized, ring_homomorphism.MapOne.Read(ringMap), module.SmulOne.Read(nModule)))
			sameAdditiveGroup := a.Have(
				"restricting the scalars keeps N's additive group",
				"module_additive_group(scalar_restriction(f, N)) = module_additive_group(N)",
				Simp(Fwd(module_record.ModuleAdditiveGroupDef)),
				Refl())
			additive := a.Have(
				"the vectors remain a group under N's addition",
				"group_on(module_additive_group(scalar_restriction(f, N)))",
				By(sameAdditiveGroup, module.AddGroupOn.Read(nModule)))
			restricted := a.TermAs[ModuleOps[A, D]]("scalar_restriction(f, N)")
			a.Show(
				"R's ring, N's group and commuting addition, and "+
					"the four laws of the action make N a module over R",
				By(
					additive,
					scaled,
					distributes,
					sumOfScalars,
					productOfScalars,
					one,
					ring_homomorphism.Source.Read(ringMap),
					module.AddComm.Read(nModule),
					module.ModuleOn.At(R, restricted)))
		}),
})}

// CoextendScalarsDef — `coextend_scalars(R, T, f, M)`: for a ring map f
// from R to T and a module M over R, the R-linear maps from T to M,
// zero off T, as a module over T — added pointwise, and scaled by t
// through the argument, (t · φ)(x) = φ(t * x) on T.
var CoextendScalarsDef = coextendScalarsDefThm{family.Define(registry.DefEntry{
	Name: "CoextendScalarsDef", Const: "coextend_scalars",
	Key:  "prop_62d6438df9d14c30",
	Type: "ring_ops(A) → ring_ops(C) → (A → C) → module_ops(A, B) → module_ops(C, C → B)",
	Equations: []string{"∀R:ring_ops(A). ∀T:ring_ops(C). ∀f:(A → C). ∀M:module_ops(A, B). coextend_scalars(R, T, f, M) = mk_module(" +
		"fun_add⟨D:C⟩(M.add), fun_zero⟨D:C⟩(M.zero), fun_neg⟨D:C⟩(M.neg), " +
		"(λt:C. λφ:(C → B). λx:C. COND(x ∈ T.carrier, φ(T.mul(t, x)), M.zero)), " +
		"hom_set(R, " + algebraOverR + ", M))"},
	Reading: "The vectors are hom_set(R, T, M) for T a module over R through f, so they are zero " +
		"off T.carrier; the scaling keeps that, reading φ at t * x on T.carrier only, where t * x may " +
		"leave T.carrier for x outside it. It is the module Hom_R(T, M) with T acting on the argument: " +
		"coextension of scalars, right adjoint to reading a T-module over R (CoextendScalarsAdjunction). " +
		"At T = R and f the identity it is Hom_R(R, M), which evaluation at R.one identifies with M.",
	Deps: []registry.EntryLike{HomSetDef},
})}

// CoextendScalarsModuleOn — the coextension of a module over R along a
// ring map to T is a module over T. Its vectors, the R-linear maps from T
// to M that vanish off T, are already a module over R under the pointwise
// sum, so what is left is the action of T through the argument: t · u is u
// after multiplying by t, R-linear because T is commutative, and each of
// its four laws is read at a point of T, off which both sides vanish.
var CoextendScalarsModuleOn = coextendScalarsModuleOnThm{family.Add(registry.ProofEntry{
	Name: "CoextendScalarsModuleOn",
	Key:  "prop_160a9815a463ec8b",
	Reading: "The ring map is what makes T a module over R, so that " +
		"hom_set(R, T, M) is the group of R-linear maps; commutativity of T is " +
		"what makes t · φ R-linear again, φ(t * (f(r) * x)) = φ(f(r) * (t * x)).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀f:(A → C). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"module_on(R, M)",
		},
		Conclusion: "module_on(T, coextend_scalars(R, T, f, M))",
		Abbrev: Abbrev{
			{Name: "vectors", Text: "hom_set(R, «algebraOverR», M)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[C]],
			f *Arrow[A, C],
			M *Expr[ModuleOps[A, B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a ring map from R to T",
				"M is a module over R")
			ringMap, ambient := parts[0], parts[1]
			ring := a.Have(
				"T is a ring on its carrier, the target of f",
				"comm_ring_on(T)",
				By(ring_homomorphism.Target.Read(ringMap)))

			// The sum, zero and negation are those of the R-linear maps from
			// T to M, a module over R.
			regularRing := a.TermAs[RingOps[C]]("T")
			regular := a.TermAs[ModuleOps[C, C]]("regular_module(T)")
			algebraOverROps := a.TermAs[ModuleOps[A, C]]("«algebraOverR»")
			overR := a.Have(
				"T, r acting as f(r), is a module over R: T over itself, its scalars restricted along f",
				"module_on(R, «algebraOverR»)",
				By(
					ringMap,
					module.RegularModuleOn.Read(ring),
					RestrictScalarsModuleOn.At(R, regularRing, f, regular)))
			maps := a.Have(
				"so the R-linear maps from T to M are a module over R",
				"module_on(R, hom_module(R, «algebraOverR», M))",
				By(overR, ambient, HomSetModuleOn))

			// T acts through the argument: c · u is u after multiplying by c
			// on T, and zero off it.
			multiplication := a.Have(
				"multiplying by a member c of T is an R-linear map from T to itself",
				"∀c:C. c ∈ T.carrier ⇒ module_homomorphism(R, «algebraOverR», «algebraOverR», λx:C. c * x)",
				Derive(func(b *Argument) {
					b.FixAs[C]("c")
					cIn := b.Assume()
					passes := b.Have(
						"c passes the scalar f(r), T being commutative",
						"∀r:A. ∀x:C. r ∈ R.carrier ∧ x ∈ T.carrier ⇒ c * (f(r) * x) = f(r) * (c * x)",
						Derive(func(e *Argument) {
							e.FixAs[A]("r")
							e.FixAs[C]("x")
							members := e.Conjuncts(
								e.Assume(),
								"r is a scalar",
								"x lies in T")
							image := e.Have(
								"f(r) lies in T",
								"f(r) ∈ T.carrier",
								By(ring_homomorphism.MapIn.Read(ringMap), members[0]))
							e.Show(
								"c, f(r) and x lie in the commutative ring T",
								ByArith(ring, cIn, image, members[1]))
						}))
					b.Show(
						"it keeps T, distributes over a sum and passes the scalars",
						By(
							overR,
							cIn,
							passes,
							comm_ring.MulIn.Read(ring),
							comm_ring.LeftDistribOn.Read(ring),
							module_homomorphism.ModuleHomomorphismDef))
				}))
			scaled := a.Have(
				"c · u is a vector: on T it is u after multiplying by c, an R-linear map, and it vanishes off T",
				Statement{
					Binders: "∀c:C. ∀u:(C → B).",
					Hypotheses: []string{
						"c ∈ T.carrier",
						"u ∈ «vectors»",
					},
					Conclusion: "(λx:C. COND(x ∈ T.carrier, u(c * x), M.zero)) ∈ «vectors»",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[C]("c"), b.FixAs[Fun[C, B]]("u")
					hypotheses := b.Conjuncts(
						b.Assume(),
						"c lies in T",
						"u is a vector")
					linear := b.Have(
						"u is R-linear",
						"module_homomorphism(R, «algebraOverR», M, u)",
						By(InHomSet.At(R, algebraOverROps, M, u), hypotheses[1]))
					times := b.TermAs[Fun[C, C]]("λx:C. c * x")
					after := b.TermAs[Fun[C, B]]("λx:C. u(c * x)")
					action := b.TermAs[Fun[C, B]]("λx:C. COND(x ∈ T.carrier, u(c * x), M.zero)")
					composite := b.Have(
						"so is u after multiplying by c, the composite of two R-linear maps",
						"module_homomorphism(R, «algebraOverR», M, λx:C. u(c * x))",
						By(
							multiplication.At(c),
							hypotheses[0],
							linear,
							module_homomorphism.HomCompose.At(R, algebraOverROps, algebraOverROps, M, times, u),
							functions.ComposeApply.At(u, times)))
					agrees := b.Have(
						"c · u agrees with it on T, so it is R-linear too",
						"module_homomorphism(R, «algebraOverR», M, λx:C. COND(x ∈ T.carrier, u(c * x), M.zero))",
						By(composite, module_homomorphism.HomCongruence.At(R, algebraOverROps, M, after, action)))
					vanishes := b.Have(
						"c · u vanishes off T, by its definition",
						"∀x:C. x ∉ T.carrier ⇒ COND(x ∈ T.carrier, u(c * x), M.zero) = M.zero",
						b.ForEach(func(_ *Expr[C]) Action { return Basic() }))
					b.Show(
						"an R-linear map that vanishes off T is a vector",
						By(InHomSet.At(R, algebraOverROps, M, action), agrees, vanishes))
				}))

			// The four laws of the action, each read at a point x: on T by the
			// ring laws of T and the additivity of u, off T both sides are zero.
			additive := module.AddGroupOn.Read(ambient)
			zeroSum := a.Have(
				"zero plus zero is zero in M",
				"M.zero + M.zero = M.zero",
				By(group.LeftIdentityOn.Read(additive), group.OneIn.Read(additive)))
			distributes := a.Have(
				"c · (u + v) = c · u + c · v for any functions: on T "+
					"both sides are u(c * x) + v(c * x), off T zero + zero",
				"∀c:C. "+
					"    ∀u v:(C → B).(λx:C. COND(x ∈ T.carrier, fun_add(u, v, c * x), M.zero)) = "+
					"    fun_add(λx:C. COND(x ∈ T.carrier, u(c * x), M.zero), "+
					"        λx:C. COND(x ∈ T.carrier, v(c * x), M.zero))",
				Derive(func(b *Argument) {
					b.FixAs[C]("c")
					b.FixAs[Fun[C, B]]("u")
					b.FixAs[Fun[C, B]]("v")
					b.Show(
						"at each x it is a sum read pointwise",
						Funext(),
						Simp(Fwd(function_module.FunAddDef)),
						By(zeroSum))
				}))
			sumOfScalars := a.Have(
				"(c + d) · u = c · u + d · u: on T, (c + d) * x = c * x + d * x and u is additive",
				Statement{
					Binders: "∀c d:C. ∀u:(C → B).",
					Hypotheses: []string{
						"c ∈ T.carrier",
						"d ∈ T.carrier",
						"u ∈ «vectors»",
					},
					Conclusion: "(λx:C. COND(x ∈ T.carrier, u((c + d) * x), M.zero)) = " +
						"fun_add(λx:C. COND(x ∈ T.carrier, u(c * x), M.zero), λx:C. COND(x ∈ T.carrier, u(d * x), M.zero))",
				},
				Derive(func(b *Argument) {
					c, d, u := b.FixAs[C]("c"), b.FixAs[C]("d"), b.FixAs[Fun[C, B]]("u")
					hypotheses := b.Conjuncts(
						b.Assume(),
						"c lies in T",
						"d lies in T",
						"u is a vector")
					linear := b.Have(
						"u is R-linear",
						"module_homomorphism(R, «algebraOverR», M, u)",
						By(InHomSet.At(R, algebraOverROps, M, u), hypotheses[2]))
					pointwise := b.Have(
						"on T, u((c + d) * x) = u(c * x) + u(d * x)",
						"∀x:C. x ∈ T.carrier ⇒ u((c + d) * x) = u(c * x) + u(d * x)",
						Derive(func(e *Argument) {
							x := e.FixAs[C]("x")
							cm, dm, xm :=
								proof.MemberOf(c, hypotheses[0]), proof.MemberOf(d, hypotheses[1]), proof.MemberOf(x, e.Assume())
							products := comm_ring.MulIn.Read(ring)
							e.Show(
								"(c + d) * x = c * x + d * x in T, and u adds at c * x and d * x",
								By(
									comm_ring.RightDistribOn.Read(ring).At(cm, dm, xm),
									module_homomorphism.HomAdd.Read(linear).At(products.At(cm, xm), products.At(dm, xm))))
						}))
					b.Show(
						"at each x it is that sum, or zero + zero off T",
						Funext(),
						Simp(Fwd(function_module.FunAddDef)),
						b.ForEach(func(y *Expr[C]) Action { return By(pointwise.At(y), zeroSum) }))
				}))
			productOfScalars := a.Have(
				"(c * d) · u = c · (d · u): on T, (c * d) * x = d * (c * x), and c * x lies in T",
				Statement{
					Binders: "∀c d:C. ∀u:(C → B).",
					Hypotheses: []string{
						"c ∈ T.carrier",
						"d ∈ T.carrier",
						"u ∈ «vectors»",
					},
					Conclusion: "(λx:C. COND(x ∈ T.carrier, u(c * d * x), M.zero)) = " +
						"λx:C. COND(x ∈ T.carrier, COND(c * x ∈ T.carrier, u(d * (c * x)), M.zero), M.zero)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[C]("c")
					b.FixAs[C]("d")
					b.FixAs[Fun[C, B]]("u")
					hypotheses := b.Conjuncts(
						b.Assume(),
						"c lies in T",
						"d lies in T",
						"u is a vector")
					regroup := b.Have(
						"(c * d) * x = d * (c * x) in the commutative ring T",
						"∀x:C. x ∈ T.carrier ⇒ (c * d) * x = d * (c * x)",
						Derive(func(e *Argument) {
							e.FixAs[C]("x")
							e.Show(
								"c, d and x lie in T",
								ByArith(ring, hypotheses[0], hypotheses[1], e.Assume()))
						}))
					b.Show(
						"at each x of T both sides are u((c * d) * x), c * x lying in T",
						Funext(),
						b.ForEach(func(y *Expr[C]) Action {
							return By(Normalized, regroup.At(y), hypotheses[0], comm_ring.MulIn.Read(ring).AsFact().At(c, y))
						}))
				}))
			one := a.Have(
				"T.one · u = u: on T, T.one * x = x, and off T both sides vanish",
				"∀u:(C → B). u ∈ «vectors» ⇒ (λx:C. COND(x ∈ T.carrier, u(T.one * x), M.zero)) = u",
				Derive(func(b *Argument) {
					u := b.FixAs[Fun[C, B]]("u")
					uIn := b.Assume()
					vanishes := b.Have(
						"u vanishes off T",
						"∀x:C. x ∉ T.carrier ⇒ u(x) = M.zero",
						By(InHomSet.At(R, algebraOverROps, M, u), uIn))
					b.Show(
						"at each x it is u(x): T.one is the identity of T, and u vanishes off T",
						Funext(),
						b.ForEach(func(y *Expr[C]) Action {
							return By(
								Normalized,
								vanishes.At(y),
								comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(y))
						}))
				}))
			sameAdditiveGroup := a.Have(
				"the coextension's additive group is that of the R-linear maps",
				"module_additive_group(coextend_scalars(R, T, f, M)) = "+
					"module_additive_group(hom_module(R, «algebraOverR», M))",
				Simp(Fwd(module_record.ModuleAdditiveGroupDef)),
				Refl())
			mapsGroup := a.Have(
				"so its vectors are a group under the pointwise sum",
				"group_on(module_additive_group(coextend_scalars(R, T, f, M)))",
				By(sameAdditiveGroup, module.AddGroupOn.Read(maps)))
			coextension := a.TermAs[ModuleOps[C, Fun[C, B]]]("coextend_scalars(R, T, f, M)")
			a.Show(
				"T's ring, the group of R-linear maps under the pointwise sum, "+
					"and the action of T with its four laws make a module over T",
				By(
					ring,
					mapsGroup,
					module.AddComm.Read(maps),
					scaled,
					distributes,
					sumOfScalars,
					productOfScalars,
					one,
					module.ModuleOn.At(T, coextension)))
		}),
})}

// CoextendScalarsAdjunction — for a ring map f from R to T, a module M
// over R and a module N over T: the T-linear maps from N into the
// coextension of M are the R-linear maps from N to M, by evaluation at
// T.one.
var CoextendScalarsAdjunction = coextendScalarsAdjunctionThm{family.Add(registry.ProofEntry{
	Name: "CoextendScalarsAdjunction",
	Key:  "prop_ff82e84b31185571",
	Reading: "The isomorphism is of modules over R, the left side Hom_T(N, coextend_scalars(R, " +
		"T, f, M)) read over R through f; the map is named, φ ↦ (n ↦ φ(n)(T.one)), and so is its " +
		"inverse, ψ ↦ (n ↦ (x ↦ ψ(x • n)) on T.carrier, zero off it) on N.carrier. Off N.carrier " +
		"φ(n) is the zero map, so the image is zero there as hom_set asks. φ is read at T.one " +
		"only: T-linearity recovers the rest, φ(n)(x) = (x · φ(n))(T.one) = φ(x • n)(T.one).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀f:(A → C). ∀M:module_ops(A, B). ∀N:module_ops(C, D).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"module_on(R, M)",
			"module_on(T, N)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    scalar_restriction(f, hom_module(T, N, coextend_scalars(R, T, f, M))), " +
			"    hom_module(R, scalar_restriction(f, N), M), " +
			"    λφ:(D → C → B). λn:D. φ(n)(T.one))",
		Abbrev: Abbrev{
			// N read over R through f, and the R-linear maps of N into M.
			{Name: "rLinear", Text: "hom_set(R, scalar_restriction(f, N), M)"},
			{Name: "coextension", Text: "coextend_scalars(R, T, f, M)"},
			{Name: "tLinearModule", Text: "hom_module(T, N, «coextension»)"},
			{Name: "tLinear", Text: "hom_set(T, N, «coextension»)"},
			{Name: "evaluation", Text: "λφ:(D → C → B). λn:D. φ(n)(T.one)"},
			{Name: "coextAction", Text: "λt:C. λψ:(C → B). λx:C. COND(x ∈ T.carrier, ψ(t * x), M.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[C]],
			f *Arrow[A, C],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[C, D]],
			given Fact,
			nModule module.ModuleFact[on.T, on.N],
		) {
			const (
				// The coextension of M along f, and the way T acts on it:
				// (t · ψ)(x) = ψ(t * x) on T.carrier, zero off it.
				coextension = "coextend_scalars(R, T, f, M)"
				// The T-linear maps of N into the coextension, and the module
				// they form over T.
				// Evaluation at T.one, the isomorphism.
			)
			parts := a.Conjuncts(
				given,
				"f is a ring homomorphism of R into T",
				"M is a module over R")
			ringMap, mModule := parts[0], parts[1]
			tRing := module.RingOn.Read(nModule)
			oneIn := comm_ring.OneIn.Read(tRing)
			coextensionOps := a.TermAs[ModuleOps[C, Fun[C, B]]]("«coextension»")
			tLinearOps := a.TermAs[ModuleOps[C, Fun[D, Fun[C, B]]]]("«tLinearModule»")
			nOverROps := a.TermAs[ModuleOps[A, D]]("scalar_restriction(f, N)")
			regularRing := a.TermAs[RingOps[C]]("T")
			regular := a.TermAs[ModuleOps[C, C]]("regular_module(T)")
			tLin := a.TermAs[Set[Fun[D, Fun[C, B]]]]("«tLinear»")
			evaluate := a.TermAs[Fun[Fun[D, Fun[C, B]], Fun[D, B]]]("«evaluation»")

			// The modules in play: the coextension and the T-linear maps
			// into it over T, and N and T itself read over R through f.
			coextensionOn := a.Have(
				"the coextension is a module over T",
				"module_on(T, «coextension»)",
				By(CoextendScalarsModuleOn.At(R, T, f, M), given))
			tLinearOn := a.Have(
				"so are the T-linear maps of N into it",
				"module_on(T, «tLinearModule»)",
				By(HomSetModuleOn.At(T, N, coextensionOps), nModule, coextensionOn))
			nOverROn := a.Have(
				"N read over R through f is a module over R",
				"module_on(R, scalar_restriction(f, N))",
				By(RestrictScalarsModuleOn.At(R, T, f, N), ringMap, nModule))
			algebraOverROn := a.Have(
				"so is T, acting on itself, read over R through f",
				"module_on(R, «algebraOverR»)",
				By(
					ringMap,
					module.RegularModuleOn.Read(tRing),
					RestrictScalarsModuleOn.At(R, regularRing, f, regular)))
			rLinearOn := a.Have(
				"so the R-linear maps of N into M are a module over R",
				"module_on(R, hom_module(R, scalar_restriction(f, N), M))",
				By(HomSetModuleOn.At(R, nOverROps, M), nOverROn, mModule))

			// The three sets of maps, read pointwise.
			tMember := a.Have(
				"a T-linear φ of N into the coextension: each φ(n) on N is "+
					"R-linear from T into M, and φ adds, is T-linear and is zero off N",
				"∀φ:(D → C → B). "+
					"    φ ∈ «tLinear» ⇔ "+
					"    (∀n:D. n ∈ N.carrier ⇒ φ(n) ∈ hom_set(R, «algebraOverR», M)) ∧ "+
					"    (∀u v:D. u ∈ N.carrier ∧ v ∈ N.carrier ⇒ φ(u + v) = fun_add(M.add, φ(u), φ(v))) ∧ "+
					"    (∀t:C. ∀n:D. "+
					"        t ∈ T.carrier ∧ n ∈ N.carrier ⇒ "+
					"        φ(t • n) = (λx:C. COND(x ∈ T.carrier, φ(n)(t * x), M.zero))) ∧ "+
					"    (∀n:D. n ∉ N.carrier ⇒ φ(n) = fun_zero(M.zero))",
				Simp(Fwd(InHomSet), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(nModule, coextensionOn))
			gMember := a.Have(
				"a member of the coextension is an R-linear map of "+
					"T, read over R through f, into M that is zero off T",
				"∀g:(C → B). "+
					"    g ∈ hom_set(R, «algebraOverR», M) ⇔ "+
					"    (∀x:C. x ∈ T.carrier ⇒ g(x) ∈ M.carrier) ∧ "+
					"    (∀x y:C. x ∈ T.carrier ∧ y ∈ T.carrier ⇒ g(x + y) = g(x) + g(y)) ∧ "+
					"    (∀r:A. ∀x:C. r ∈ R.carrier ∧ x ∈ T.carrier ⇒ g(f(r) * x) = r • g(x)) ∧ "+
					"    (∀x:C. x ∉ T.carrier ⇒ g(x) = M.zero)",
				Simp(Fwd(InHomSet), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(algebraOverROn, mModule))
			rMember := a.Have(
				"a member of Hom_R(N, M) is an R-linear map of N, read over R through f, into M that is zero off N",
				"∀ψ:(D → B). "+
					"    ψ ∈ «rLinear» ⇔ "+
					"    (∀n:D. n ∈ N.carrier ⇒ ψ(n) ∈ M.carrier) ∧ "+
					"    (∀u v:D. u ∈ N.carrier ∧ v ∈ N.carrier ⇒ ψ(u + v) = ψ(u) + ψ(v)) ∧ "+
					"    (∀r:A. ∀n:D. r ∈ R.carrier ∧ n ∈ N.carrier ⇒ ψ(f(r) • n) = r • ψ(n)) ∧ "+
					"    (∀n:D. n ∉ N.carrier ⇒ ψ(n) = M.zero)",
				Simp(Fwd(InHomSet), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(nOverROn, mModule))

			// Evaluation at T.one lands in Hom_R(N, M), and is R-linear:
			// it adds, and carries the scaling by f(c) to the scaling by c.
			lands := a.Have(
				"evaluation at T.one carries a T-linear map of N "+
					"into the coextension to an R-linear map of N into M",
				"∀φ:(D → C → B). φ ∈ «tLinear» ⇒ (λn:D. φ(n)(T.one)) ∈ «rLinear»",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[D, Fun[C, B]]]()
					φIn := b.Assume()
					linear := tMember.At(φ)
					values := b.Have(
						"its values lie in M: on N, φ(n) is an R-linear map of T into M, and T.one lies in T",
						"∀n:D. n ∈ N.carrier ⇒ φ(n)(T.one) ∈ M.carrier",
						Derive(func(c *Argument) {
							c.FixAs[D]()
							nIn := c.Assume()
							c.Show(
								"φ(n) carries T.one into M",
								By(linear, φIn, nIn, gMember.At(c.TermAs[Fun[C, B]]("φ(n)")), oneIn))
						}))
					sums := b.Have(
						"it adds: φ carries a sum to the pointwise sum",
						"∀u v:D. u ∈ N.carrier ∧ v ∈ N.carrier ⇒ φ(u + v)(T.one) = φ(u)(T.one) + φ(v)(T.one)",
						By(linear, φIn, function_module.FunAddDef))
					scalings := b.Have(
						"it is R-linear: φ(f(r) • n) is f(r) acting on φ(n), which at T.one reads φ(n) at f(r) * T.one",
						"∀r:A. ∀n:D. r ∈ R.carrier ∧ n ∈ N.carrier ⇒ φ(f(r) • n)(T.one) = r • φ(n)(T.one)",
						Derive(func(c *Argument) {
							c.FixAs[A]()
							c.FixAs[D]()
							members := c.Assume()
							image := c.Have(
								"f(r) lies in T",
								"f(r) ∈ T.carrier",
								By(ring_homomorphism.MapIn.Read(ringMap), members))
							c.Show(
								"at T.one the coextension's action reads φ(n) at "+
									"f(r) * T.one, which φ(n) carries to r • φ(n)(T.one)",
								By(linear, φIn, gMember.At(c.TermAs[Fun[C, B]]("φ(n)")), members, image, oneIn))
						}))
					zeroOff := b.Have(
						"off N it is zero, φ being zero there",
						"∀n:D. n ∉ N.carrier ⇒ φ(n)(T.one) = M.zero",
						By(linear, φIn, function_module.FunZeroDef))
					b.Show(
						"so it is an R-linear map of N into M, zero off N",
						By(rMember.At(b.TermAs[Fun[D, B]]("λn:D. φ(n)(T.one)")), values, sums, scalings, zeroOff))
				}))
			adds := a.Have(
				"evaluation carries the pointwise sum of two T-linear "+
					"maps to the pointwise sum of their evaluations",
				Statement{
					Binders: "∀φ χ:(D → C → B).",
					Hypotheses: []string{
						"φ ∈ «tLinear»",
						"χ ∈ «tLinear»",
					},
					Conclusion: "(λn:D. fun_add(fun_add(M.add), φ, χ)(n)(T.one)) = " +
						"fun_add(M.add, λn:D. φ(n)(T.one), λn:D. χ(n)(T.one))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Fun[C, B]]]()
					b.FixAs[Fun[D, Fun[C, B]]]()
					b.Assume()
					b.Show(
						"at each n both sides are φ(n)(T.one) + χ(n)(T.one)",
						Funext(),
						Simp(Fwd(function_module.FunAddDef)),
						Basic())
				}))
			scales := a.Have(
				"evaluation carries the coextension's scaling by f(c) to the scaling by c",
				Statement{
					Binders: "∀c:A. ∀φ:(D → C → B).",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"φ ∈ «tLinear»",
					},
					Conclusion: "(λn:D. fun_smul(«coextAction», f(c), φ)(n)(T.one)) = " +
						"fun_smul(M.smul, c, λn:D. φ(n)(T.one))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					φ := b.FixAs[Fun[D, Fun[C, B]]]()
					given := b.Assume()
					b.Do(Funext(), Simp(Fwd(function_module.FunSmulDef)))
					b.FixAs[D]("n")
					b.Cases(b.Term("n ∈ N.carrier"))
					b.When(
						"on N, φ(n) is R-linear on T read through f, so it carries f(c) * T.one to c • φ(n)(T.one)",
						func(e *Argument, nIn Fact) {
							e.Show(
								"the action at T.one reads φ(n) at f(c) * T.one",
								By(tMember.At(φ), gMember.At(e.TermAs[Fun[C, B]]("φ(n)")), given, nIn, oneIn))
						})
					b.Otherwise(
						"off N, φ(n) is the zero map, and c • M.zero is M.zero",
						func(e *Argument, nOut Fact) {
							e.Show(
								"both sides are M.zero",
								By(tMember.At(φ), given, nOut, function_module.FunZeroDef, module.SmulZero.Read(mModule)))
						})
				}))

			// One-to-one: on N and T, φ(n)(x) is φ(x • n) read at T.one;
			// off N, or off T, it is zero.
			recovered := a.Have(
				"on N and T a T-linear map into the coextension is read off its "+
					"evaluation: φ(x • n) is x acting on φ(n), which at T.one reads φ(n) at x",
				Statement{
					Binders: "∀φ:(D → C → B). ∀n:D. ∀x:C.",
					Hypotheses: []string{
						"φ ∈ «tLinear»",
						"n ∈ N.carrier",
						"x ∈ T.carrier",
					},
					Conclusion: "φ(n)(x) = φ(x • n)(T.one)",
				},
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[D, Fun[C, B]]]()
					b.FixAs[D]()
					b.FixAs[C]()
					given := b.Assume()
					b.Show(
						"φ(x • n)(T.one) is φ(n)(x * T.one), and x * T.one is x",
						By(
							tMember.At(φ),
							given,
							oneIn,
							comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(tRing))))
				}))
			zeroOffN := a.Have(
				"off N a T-linear map into the coextension is the zero map",
				"∀φ:(D → C → B). ∀n:D. ∀x:C. φ ∈ «tLinear» ∧ n ∉ N.carrier ⇒ φ(n)(x) = M.zero",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[D, Fun[C, B]]]()
					b.FixAs[D]()
					b.FixAs[C]()
					given := b.Assume()
					b.Show(
						"φ(n) is the zero map",
						By(tMember.At(φ), given, function_module.FunZeroDef))
				}))
			zeroOffT := a.Have(
				"on N its values φ(n)(x) are zero off T, φ(n) being an R-linear map of T into M",
				"∀φ:(D → C → B). ∀n:D. ∀x:C. φ ∈ «tLinear» ∧ n ∈ N.carrier ∧ x ∉ T.carrier ⇒ φ(n)(x) = M.zero",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[D, Fun[C, B]]]()
					b.FixAs[D]()
					b.FixAs[C]()
					given := b.Assume()
					b.Show(
						"φ(n) lies in the coextension, whose members are zero off T",
						By(tMember.At(φ), given, gMember.At(b.TermAs[Fun[C, B]]("φ(n)"))))
				}))
			injective := a.Have(
				"evaluation at T.one is one-to-one on the T-linear maps",
				"injective_on(«tLinear», «evaluation»)",
				Derive(func(b *Argument) {
					agree := b.Have(
						"two T-linear maps with one evaluation agree at every n and x",
						Statement{
							Binders: "∀φ χ:(D → C → B).",
							Hypotheses: []string{
								"φ ∈ «tLinear»",
								"χ ∈ «tLinear»",
								"(λn:D. φ(n)(T.one)) = λn:D. χ(n)(T.one)",
							},
							Conclusion: "φ = χ",
						},
						Derive(func(c *Argument) {
							φ, χ := c.FixAs[Fun[D, Fun[C, B]]](), c.FixAs[Fun[D, Fun[C, B]]]()
							given := c.Assume()
							c.Do(Funext())
							n, x := c.FixAs[D]("n"), c.FixAs[C]("x")
							c.Cases(c.Term("n ∈ N.carrier ∧ x ∈ T.carrier"))
							c.When(
								"on N and T both are read off the common evaluation at x • n",
								func(e *Argument, inside Fact) {
									e.Show(
										"φ(n)(x) and χ(n)(x) are the two evaluations at x • n",
										By(recovered.At(φ, n, x), recovered.At(χ, n, x), given, inside))
								})
							c.Otherwise(
								"off N or off T both are M.zero",
								func(e *Argument, outside Fact) {
									e.Show(
										"φ(n)(x) and χ(n)(x) are M.zero",
										By(
											zeroOffN.At(φ, n, x),
											zeroOffN.At(χ, n, x),
											zeroOffT.At(φ, n, x),
											zeroOffT.At(χ, n, x),
											given,
											outside))
								})
						}))
					b.Show(
						"which is injectivity on the T-linear maps",
						By(functions.InjectiveOnDef.At(tLin, evaluate), agree))
				}))

			// Onto: an R-linear ψ is the evaluation of the T-linear map
			// θ(n)(x) = ψ(x • n) for n in N and x in T, zero elsewhere.
			onto := a.Have(
				"every R-linear map of N into M is the evaluation of a T-linear map into the coextension",
				"image(«evaluation», «tLinear») = «rLinear»",
				Derive(func(b *Argument) {
					extends := b.Have(
						"each R-linear ψ is the evaluation of n ↦ (x ↦ ψ(x • n)) on N and T, zero elsewhere",
						"∀ψ:(D → B). ψ ∈ «rLinear» ⇒ ψ ∈ image(«evaluation», «tLinear»)",
						Derive(func(c *Argument) {
							ψ := c.FixAs[Fun[D, B]]()
							ψIn := c.Assume()
							ψParts := c.Conjuncts(
								c.Have(
									"ψ carries N into M, adds, is R-linear through f, and is zero off N",
									"(∀n:D. n ∈ N.carrier ⇒ ψ(n) ∈ M.carrier) ∧ "+
										"(∀u v:D. u ∈ N.carrier ∧ v ∈ N.carrier ⇒ ψ(u + v) = ψ(u) + ψ(v)) ∧ "+
										"(∀r:A. ∀n:D. r ∈ R.carrier ∧ n ∈ N.carrier ⇒ ψ(f(r) • n) = r • ψ(n)) ∧ "+
										"(∀n:D. n ∉ N.carrier ⇒ ψ(n) = M.zero)",
									By(rMember.At(ψ), ψIn)),
								"ψ carries N into M",
								"ψ adds",
								"ψ is R-linear through f",
								"ψ is zero off N")
							ψValues, ψSums, ψScalings, ψZero := ψParts[0], ψParts[1], ψParts[2], ψParts[3]
							θ, θDef := c.LetAs[Fun[D, Fun[C, B]]](
								"θ", "λn:D. λx:C. COND(n ∈ N.carrier ∧ x ∈ T.carrier, ψ(x • n), M.zero)")
							θOn := c.Have(
								"on N and T, θ(n)(x) is ψ(x • n)",
								"∀n:D. ∀x:C. n ∈ N.carrier ∧ x ∈ T.carrier ⇒ θ(n)(x) = ψ(x • n)",
								By(Normalized, θDef))
							θOffN := c.Have(
								"off N, θ(n)(x) is M.zero",
								"∀n:D. ∀x:C. n ∉ N.carrier ⇒ θ(n)(x) = M.zero",
								By(Normalized, θDef))
							θOffT := c.Have(
								"off T, θ(n)(x) is M.zero",
								"∀n:D. ∀x:C. x ∉ T.carrier ⇒ θ(n)(x) = M.zero",
								By(Normalized, θDef))
							scalarsIn := module.SmulIn.Read(nModule)

							θLinear := c.Have(
								"on N, θ(n) is an R-linear map of T into M: x ↦ ψ(x • n) adds by "+
									"the distributivity of N, and moves f(r) out by the R-linearity of ψ",
								"∀n:D. n ∈ N.carrier ⇒ θ(n) ∈ hom_set(R, «algebraOverR», M)",
								Derive(func(d *Argument) {
									n := d.FixAs[D]()
									nm := d.MemberOf[on.N](n, d.Assume())
									intoM := d.Have(
										"θ(n) carries T into M",
										"∀x:C. x ∈ T.carrier ⇒ θ(n)(x) ∈ M.carrier",
										d.ForEach(func(x *Expr[C]) Action {
											return By(θOn.At(n, x), nm, ψValues, scalarsIn)
										}))
									adds := d.Have(
										"θ(n) adds: (x + y) • n = x • n + y • n",
										"∀x y:C. x ∈ T.carrier ∧ y ∈ T.carrier ⇒ θ(n)(x + y) = θ(n)(x) + θ(n)(y)",
										Derive(func(e *Argument) {
											x, y := e.FixAs[C](), e.FixAs[C]()
											xy := e.Conjuncts(
												e.Assume(),
												"x lies in T",
												"y lies in T")
											xm, ym := e.MemberOf[on.T](x, xy[0]), e.MemberOf[on.T](y, xy[1])
											sum := comm_ring.AddIn.Read(tRing).At(xm, ym)
											xn, yn := scalarsIn.At(xm, nm), scalarsIn.At(ym, nm)
											e.Show(
												"ψ adds at x • n and y • n",
												By(
													θOn.At(n, sum),
													θOn.At(n, x),
													θOn.At(n, y),
													nm,
													sum,
													xm,
													ym,
													module.SmulAddRight.Read(nModule).At(xm, ym, nm),
													ψSums.At(xn, yn),
													xn,
													yn))
										}))
									scales := d.Have(
										"θ(n) is R-linear: (f(r) * x) • n = f(r) • (x • n)",
										"∀r:A. ∀x:C. r ∈ R.carrier ∧ x ∈ T.carrier ⇒ θ(n)(f(r) * x) = r • θ(n)(x)",
										Derive(func(e *Argument) {
											r, x := e.FixAs[A](), e.FixAs[C]()
											rx := e.Conjuncts(
												e.Assume(),
												"r is a scalar of R",
												"x lies in T")
											xm := e.MemberOf[on.T](x, rx[1])
											image := e.Have(
												"f(r) lies in T",
												"f(r) ∈ T.carrier",
												By(ring_homomorphism.MapIn.Read(ringMap), rx[0]))
											fr := e.MemberOf[on.T](e.TermAs[C]("f(r)"), image)
											product := comm_ring.MulIn.Read(tRing).At(fr, xm)
											xn := scalarsIn.At(xm, nm)
											e.Show(
												"ψ moves f(r) out of x • n as r",
												By(
													θOn.At(n, product),
													θOn.At(n, x),
													nm,
													product,
													xm,
													module.SmulMul.Read(nModule).At(fr, xm, nm),
													ψScalings.At(r, xn),
													rx[0],
													xn))
										}))
									zeroOff := d.Have(
										"θ(n) is zero off T",
										"∀x:C. x ∉ T.carrier ⇒ θ(n)(x) = M.zero",
										d.ForEach(func(x *Expr[C]) Action { return By(θOffT.At(n, x)) }))
									d.Show(
										"so θ(n) lies in the coextension",
										By(gMember.At(d.TermAs[Fun[C, B]]("θ(n)")), intoM, adds, scales, zeroOff))
								}))
							θSums := c.Have(
								"θ adds: x • (u + v) = x • u + x • v on T, and off T both sides are M.zero",
								"∀u v:D. u ∈ N.carrier ∧ v ∈ N.carrier ⇒ θ(u + v) = fun_add(M.add, θ(u), θ(v))",
								Derive(func(d *Argument) {
									u, v := d.FixAs[D](), d.FixAs[D]()
									uv := d.Conjuncts(
										d.Assume(),
										"u lies in N",
										"v lies in N")
									um, vm := d.MemberOf[on.N](u, uv[0]), d.MemberOf[on.N](v, uv[1])
									d.Do(Funext(), Simp(Fwd(function_module.FunAddDef)))
									x := d.FixAs[C]("x")
									sum := group.MulIn.Read(module.AddGroupOn.Read(nModule)).At(um, vm)
									d.Cases(d.Term("x ∈ T.carrier"))
									d.When(
										"on T, ψ adds at x • u and x • v",
										func(e *Argument, xIn Fact) {
											xm := e.MemberOf[on.T](x, xIn)
											xu, xv := scalarsIn.At(xm, um), scalarsIn.At(xm, vm)
											e.Show(
												"θ(u + v)(x) is ψ(x • u) + ψ(x • v)",
												By(
													θOn.At(sum, x),
													θOn.At(u, x),
													θOn.At(v, x),
													sum,
													xm,
													module.SmulAddLeft.Read(nModule).At(xm, um, vm),
													ψSums.At(xu, xv),
													xu,
													xv))
										})
									d.Otherwise(
										"off T, M.zero is M.zero + M.zero",
										func(e *Argument, xOut Fact) {
											additive := module.AddGroupOn.Read(mModule)
											e.Show(
												"all three values are M.zero",
												By(
													Normalized,
													θOffT.At(sum, x),
													θOffT.At(u, x),
													θOffT.At(v, x),
													xOut,
													group.LeftIdentityOn.Read(additive),
													group.OneIn.Read(additive)))
										})
								}))
							θScalings := c.Have(
								"θ moves the scalars of T into the argument: x • (t • n) = (t * x) • n, T being commutative",
								Statement{
									Binders: "∀t:C. ∀n:D.",
									Hypotheses: []string{
										"t ∈ T.carrier",
										"n ∈ N.carrier",
									},
									Conclusion: "θ(t • n) = λx:C. COND(x ∈ T.carrier, θ(n)(t * x), M.zero)",
								},
								Derive(func(d *Argument) {
									t, n := d.FixAs[C](), d.FixAs[D]()
									tn := d.Conjuncts(
										d.Assume(),
										"t lies in T",
										"n lies in N")
									tm, nm := d.MemberOf[on.T](t, tn[0]), d.MemberOf[on.N](n, tn[1])
									scaled := scalarsIn.At(tm, nm)
									d.Do(Funext())
									x := d.FixAs[C]("x")
									d.Cases(d.Term("x ∈ T.carrier"))
									d.When(
										"on T, both sides are ψ at (x * t) • n",
										func(e *Argument, xIn Fact) {
											xm := e.MemberOf[on.T](x, xIn)
											product := comm_ring.MulIn.Read(tRing).At(tm, xm)
											e.Show(
												"x • (t • n) is (x * t) • n, and x * t is t * x",
												By(
													θOn.At(scaled, x),
													θOn.At(n, product),
													scaled,
													xm,
													product,
													nm,
													module.SmulMul.Read(nModule).At(xm, tm, nm),
													comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(tRing)).At(xm, tm)))
										})
									d.Otherwise(
										"off T, both sides are M.zero",
										func(e *Argument, xOut Fact) {
											e.Show(
												"θ(t • n) is zero off T",
												By(θOffT.At(scaled, x), xOut))
										})
								}))
							θZero := c.Have(
								"θ is zero off N",
								"∀n:D. n ∉ N.carrier ⇒ θ(n) = fun_zero(M.zero)",
								Derive(func(d *Argument) {
									n := d.FixAs[D]()
									nOut := d.Assume()
									d.Do(Funext(), Simp(Fwd(function_module.FunZeroDef)))
									x := d.FixAs[C]("x")
									d.Show(
										"θ(n)(x) is M.zero",
										By(θOffN.At(n, x), nOut))
								}))
							θIn := c.Have(
								"so θ is a T-linear map of N into the coextension",
								"θ ∈ «tLinear»",
								By(tMember.At(θ), θLinear, θSums, θScalings, θZero))
							evaluates := c.Have(
								"its evaluation at T.one is ψ: T.one • n = n on N, and off N both are M.zero",
								"ψ = (λn:D. θ(n)(T.one))",
								Derive(func(d *Argument) {
									d.Do(Funext())
									n := d.FixAs[D]("n")
									d.Cases(d.Term("n ∈ N.carrier"))
									d.When(
										"on N, T.one • n is n",
										func(e *Argument, nIn Fact) {
											e.Show(
												"θ(n)(T.one) is ψ(T.one • n), which is ψ(n)",
												By(Normalized, θOn.At(n, e.TermAs[C]("T.one")), nIn, oneIn, module.SmulOne.Read(nModule)))
										})
									d.Otherwise(
										"off N, ψ(n) is M.zero",
										func(e *Argument, nOut Fact) {
											e.Show(
												"θ(n)(T.one) is M.zero too",
												By(Normalized, θOffN.At(n, e.TermAs[C]("T.one")), nOut, ψZero))
										})
								}))
							c.Show(
								"so ψ is the evaluation of θ, a point of the image",
								evaluates.Rw(),
								By(set_image.FunInImage.At(evaluate, tLin, θ), θIn))
						}))
					b.Show(
						"evaluation lands in the R-linear maps and reaches each of them",
						BySets(extends, lands))
				}))

			// The rest is the definitions: spelled out, every condition of
			// an isomorphism and of a homomorphism is a fact above, and the
			// T-linear maps, read over R through f, are a module over R.
			a.Show(
				"evaluation at T.one is an isomorphism of modules over R",
				Simp(Fwd(module_homomorphism.ModuleIsomorphismDef), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(
					RestrictScalarsModuleOn.At(R, T, f, tLinearOps),
					ringMap,
					tLinearOn,
					rLinearOn,
					lands,
					adds,
					scales,
					injective,
					onto))
		}),
})}
