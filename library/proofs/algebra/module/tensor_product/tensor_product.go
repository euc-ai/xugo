// tensor_product.go — the tensor product of two modules on sets over
// one ring: the free module on the pairs, modulo the submodule the
// bilinearity relations span. Its members are cosets, at the type
// set(prod(B, C) → A), of functions on the pairs; finite support is the
// free module's carrier, not a type. The pure tensor u ⊗ v is the coset of
// the generator at (u, v); a bilinear map out of the pairs induces one
// homomorphism out of the tensor product.

package tensor_product

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// _PairFunction is the type of a member of the free module on the
// pairs: a function on prod(B, C) into the ring.
type _PairFunction = Fun[Prod[B, C], A]

// The free module on the pairs of M × N lives at prod(B, C) → A, the
// ring's operations read pointwise; these spell its carrier and its
// record.
const pairFree = "finite_supp(R.zero, R.carrier, set_cross(M.carrier, N.carrier))"
const pairRecord = "free_module_record(R, set_cross(M.carrier, N.carrier))"

// The four kinds of relation element, at points u, u' of M, v, v' of N
// and a scalar c of R, and each kind as the set of its instances;
// relationElements is the union of the four, the set that spans
// tensor_relations.
const additiveLeftRelation = "fun_add⟨D:prod(B, C)⟩(R.add, delta_at(R.zero, " +
	"R.one, (u + u', v)), fun_neg⟨D:prod(B, C)⟩(R.neg, fun_add⟨D:prod(B, " +
	"C)⟩(R.add, delta_at(R.zero, R.one, (u, v)), delta_at(R.zero, R.one, (u', v)))))"
const additiveRightRelation = "fun_add⟨D:prod(B, C)⟩(R.add, delta_at(R.zero, " +
	"R.one, (u, v + v')), fun_neg⟨D:prod(B, C)⟩(R.neg, fun_add⟨D:prod(B, " +
	"C)⟩(R.add, delta_at(R.zero, R.one, (u, v)), delta_at(R.zero, R.one, (u, v')))))"
const scaledLeftRelation = "fun_add⟨D:prod(B, C)⟩(R.add, delta_at(R.zero, R.one, (c • u, v)), " +
	"fun_neg⟨D:prod(B, C)⟩(R.neg, fun_smul⟨D:prod(B, C)⟩(R.mul, c, delta_at(R.zero, R.one, (u, v)))))"
const scaledRightRelation = "fun_add⟨D:prod(B, C)⟩(R.add, delta_at(R.zero, R.one, (u, c • v)), " +
	"fun_neg⟨D:prod(B, C)⟩(R.neg, fun_smul⟨D:prod(B, C)⟩(R.mul, c, delta_at(R.zero, R.one, (u, v)))))"
const additiveLeftRelations = "{r:(prod(B, C) → A) | ∃u u':B. ∃v:C. u ∈ M.carrier ∧ u' ∈ M.carrier ∧ v ∈ N.carrier ∧ r = " + additiveLeftRelation + "}"
const additiveRightRelations = "{r:(prod(B, C) → A) | ∃u:B. ∃v v':C. u ∈ M.carrier ∧ v ∈ N.carrier ∧ v' ∈ N.carrier ∧ r = " + additiveRightRelation + "}"
const scaledLeftRelations = "{r:(prod(B, C) → A) | ∃c:A. ∃u:B. ∃v:C. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ∧ r = " + scaledLeftRelation + "}"
const scaledRightRelations = "{r:(prod(B, C) → A) | ∃c:A. ∃u:B. ∃v:C. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ∧ r = " + scaledRightRelation + "}"
const relationElements = additiveLeftRelations + " ∪ " + additiveRightRelations + " ∪ " + scaledLeftRelations + " ∪ " + scaledRightRelations

// binders is the definitions' common ∀-prefix: the ring and the two
// modules, each one value.
const binders = "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). "
const tensorType = "ring_ops(A) → module_ops(A, B) → module_ops(A, C) → "

// tensorRelationsDef — `tensor_relations(R, M, N)`: the submodule of the
// free module on M × N that the bilinearity relations span.
var tensorRelationsDef = tensorRelationsDefThm{family.Define(registry.DefEntry{
	Name:  "tensorRelationsDef",
	Key:   "prop_c96dfca75860f3ef",
	Const: "tensor_relations",
	Type:  tensorType + "set(prod(B, C) → A)",
	Equations: []string{
		binders + "tensor_relations(R, M, N) = module_span(R, " + pairRecord + ", " + relationElements + ")",
	},
})}

// TensorProductDef — `tensor_product(R, M, N)`: the cosets of the
// relations in the free module on the pairs.
var TensorProductDef = tensorProductDefThm{family.Define(registry.DefEntry{
	Name:  "TensorProductDef",
	Key:   "prop_95aec1cabfaf4e05",
	Const: "tensor_product",
	Type:  tensorType + "set(set(prod(B, C) → A))",
	Equations: []string{
		binders + "tensor_product(R, M, N) = left_cosets(fun_add⟨D:prod(B, C)⟩(R.add), " + pairFree + ", tensor_relations(R, M, N))",
	},
	Deps: []registry.EntryLike{tensorRelationsDef},
})}

// TensorDef — `tensor(R, M, N, u, v)`: the pure tensor u ⊗ v, the coset
// of the generator at (u, v).
var TensorDef = tensorDefThm{family.Define(registry.DefEntry{
	Name:  "TensorDef",
	Key:   "prop_118291a2c30c30fa",
	Const: "tensor",
	Type:  tensorType + "B → C → set(prod(B, C) → A)",
	Equations: []string{
		binders + "∀u:B. ∀v:C. tensor(R, M, N, u, v) = left_coset(fun_add⟨D:prod(B, C)⟩(R.add), delta_at(R.zero, R.one, (u, v)), tensor_relations(R, M, N))",
	},
	Deps: []registry.EntryLike{tensorRelationsDef},
})}

// TensorModuleDef — `tensor_module(R, M, N)`: the tensor product with its
// quotient module operations, as a module record.
var TensorModuleDef = tensorModuleDefThm{family.Define(registry.DefEntry{
	Name: "TensorModuleDef", Const: "tensor_module",
	Key:  "prop_abbe6d41a4c350d0",
	Type: tensorType + "module_ops(A, set(prod(B, C) → A))",
	Equations: []string{
		binders + "tensor_module(R, M, N) = quotient_module(" + pairRecord + ", tensor_relations(R, M, N))",
	},
	Deps: []registry.EntryLike{tensorRelationsDef},
})}

// TensorModuleCarrier — the tensor module's points are the tensor
// product: the quotient of the free module carries the cosets of the
// relations in the free module's carrier.
var TensorModuleCarrier = tensorModuleCarrierThm{family.Add(registry.ProofEntry{
	Name: "TensorModuleCarrier",
	Key:  "prop_4367bc00316d427",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Conclusion: "tensor_module(R, M, N).carrier = tensor_product(R, M, N)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N *Expr[ModuleOps[A, C]]) {
			a.Show(
				"the quotient's carrier is the cosets in the free module's carrier, the tensor product",
				Simp(Fwd(TensorModuleDef), Fwd(submodule.QuotientModuleDef), Fwd(TensorProductDef)),
				Basic())
		}),
})}

// TensorModuleAdd — addition of the tensor module is the sum of cosets
// under the free module's pointwise addition.
var TensorModuleAdd = tensorModuleAddThm{family.Add(registry.ProofEntry{
	Name: "TensorModuleAdd",
	Key:  "prop_4fcae030705bac96",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Conclusion: "tensor_module(R, M, N).add = set_mul(fun_add⟨D:prod(B, C)⟩(R.add))",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N *Expr[ModuleOps[A, C]]) {
			a.Show(
				"the quotient adds cosets as sets, under the free module's addition",
				Simp(Fwd(TensorModuleDef), Fwd(submodule.QuotientModuleDef)),
				Basic())
		}),
})}

// TensorModuleZero — the zero of the tensor module is the coset of the
// relations themselves.
var TensorModuleZero = tensorModuleZeroThm{family.Add(registry.ProofEntry{
	Name: "TensorModuleZero",
	Key:  "prop_73622af33469e0f0",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Conclusion: "tensor_module(R, M, N).zero = tensor_relations(R, M, N)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N *Expr[ModuleOps[A, C]]) {
			a.Show(
				"the quotient's zero is the submodule divided out",
				Simp(Fwd(TensorModuleDef), Fwd(submodule.QuotientModuleDef)),
				Basic())
		}),
})}

// TensorModuleSmul — a scalar acts on the tensor module by quotient
// scaling under the free module's pointwise operations.
var TensorModuleSmul = tensorModuleSmulThm{family.Add(registry.ProofEntry{
	Name: "TensorModuleSmul",
	Key:  "prop_276f326f75f9eb02",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Conclusion: "tensor_module(R, M, N).smul = " +
			"quotient_smul(fun_add⟨D:prod(B, C)⟩(R.add), " +
			"    fun_smul⟨D:prod(B, C)⟩(R.mul), " +
			"    tensor_relations(R, M, N))",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N *Expr[ModuleOps[A, C]]) {
			a.Show(
				"the quotient scales cosets by quotient_smul of the free module's operations",
				Simp(Fwd(TensorModuleDef), Fwd(submodule.QuotientModuleDef)),
				Basic())
		}),
})}

// PairGeneratorIn — the generator at a pair of M × N lies in the free
// module on the pairs: a generator lies in the free module on any set
// holding its point.
var PairGeneratorIn = pairGeneratorInThm{family.Add(registry.ProofEntry{
	Name: "PairGeneratorIn",
	Key:  "prop_ac9b5f2a26373023",
	Build: family.Theorem(comm_ring.CommRingOn.Statement(Statement{
		Binders:    "∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀u:B. ∀v:C.",
		Hypotheses: []string{"u ∈ M.carrier", "v ∈ N.carrier"},
		Conclusion: "delta_at((u, v)) ∈ «pairFree»",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			ring comm_ring.CommRingFact[on.R],
			u *Member[B, on.M],
			v *Member[C, on.N],
		) {
			a.Show(
				"(u, v) lies in M × N, and the generator at a point of a set lies in the free module on it",
				By(
					u,
					v,
					set_product.InCross.At(a.TermAs[Set[B]]("M.carrier"), a.TermAs[Set[C]]("N.carrier"), u, v),
					free_module.DeltaAtIn.Read(ring).At(
						a.TermAs[Set[Prod[B, C]]]("set_cross(M.carrier, N.carrier)"),
						a.TermAs[Prod[B, C]]("(u, v)"))))
		}),
})}

// TensorRelationKinds — a set holding the four kinds of relation element
// holds them all: the relation elements are the union of the four kinds, and
// an element of a kind is an instance of that kind's hypothesis.
var TensorRelationKinds = tensorRelationKindsThm{family.Add(registry.ProofEntry{
	Name: "TensorRelationKinds",
	Key:  "prop_79df6bb6c6c600b8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀P:set(prod(B, C) → A).",
		Hypotheses: []string{
			"∀u u':B. ∀v:C. " +
				"    u ∈ M.carrier ∧ u' ∈ M.carrier ∧ v ∈ N.carrier ⇒ «additiveLeftRelation»(u, u', v) ∈ P",
			"∀u:B. ∀v v':C. " +
				"    u ∈ M.carrier ∧ v ∈ N.carrier ∧ v' ∈ N.carrier ⇒ «additiveRightRelation»(u, v, v') ∈ P",
			"∀c:A. ∀u:B. ∀v:C. " +
				"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ «scaledLeftRelation»(c, u, v) ∈ P",
			"∀c:A. ∀u:B. ∀v:C. " +
				"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ «scaledRightRelation»(c, u, v) ∈ P",
		},
		Conclusion: "«relationElements» ⊆ P",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			P *Expr[Set[_PairFunction]],
			additiveLeft, additiveRight, scaledLeft, scaledRight Fact,
		) {
			a.Show(
				"the relation elements are the union of the four kinds, and each kind lies in P by its hypothesis",
				Simp(Fwd(set_order.UnionSubset)),
				SplitConjAll(
					Case(
						"a scaling relation in the second argument is an instance of its hypothesis",
						BySets(scaledRight)),
					Case(
						"a scaling relation in the first argument is an instance of its hypothesis",
						BySets(scaledLeft)),
					Case(
						"an additivity relation in the first argument is an instance of its hypothesis",
						BySets(additiveLeft)),
					Case(
						"an additivity relation in the second argument is an instance of its hypothesis",
						BySets(additiveRight))))
		}),
})}

// TensorRelationsSubmodule — the relations are a submodule of the free
// module on the pairs: every relation element lies in that module, so the
// submodule they span is defined there.
var TensorRelationsSubmodule = tensorRelationsSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "TensorRelationsSubmodule",
	Key:  "prop_cb59092994ec9cc9",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C).",
		Hypotheses: []string{"module_on(R, N)"},
		Conclusion: "submodule(R, «pairRecord», tensor_relations(R, M, N))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
		) {
			ring := module.RingOn.Read(mModule)
			free := a.Have(
				"the functions of finite support on M × N form an R-module",
				"module_on(R, «pairRecord»)",
				By(ring, free_module.FreeModuleOn))
			additive := module.AddGroupOn.Read(free)
			differences := a.Have(
				"the free module is closed under differences",
				"∀f g:(prod(B, C) → A). f ∈ «pairFree» ∧ g ∈ «pairFree» ⇒ fun_add(f, fun_neg(g)) ∈ «pairFree»",
				By(group.MulIn.Read(additive), group.InvIn.Read(additive)))
			generatorIn := PairGeneratorIn.Read(ring)

			additiveLeft := a.Have(
				"the additivity relation at u, u' and v lies in the free module",
				Statement{
					Binders:    "∀u u':B. ∀v:C.",
					Hypotheses: []string{"u ∈ M.carrier", "u' ∈ M.carrier", "v ∈ N.carrier"},
					Conclusion: "«additiveLeftRelation»(u, u', v) ∈ «pairFree»",
				},
				Derive(func(b *Argument) {
					u, uPrime, v := b.FixAs[B]("u"), b.FixAs[B]("u'"), b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"addition in M keeps the new pair in M × N, and sums and differences stay in the free module",
						By(
							group.MulIn.Read(additive),
							members,
							generatorIn.At(M, N, b.TermAs[B]("u + u'"), v),
							generatorIn.At(M, N, u, v),
							generatorIn.At(M, N, uPrime, v),
							differences,
							group.MulIn.Read(module.AddGroupOn.Read(mModule)).AsFact().At(u, uPrime)))
				}))
			additiveRight := a.Have(
				"the additivity relation at u, v and v' lies in the free module",
				Statement{
					Binders:    "∀u:B. ∀v v':C.",
					Hypotheses: []string{"u ∈ M.carrier", "v ∈ N.carrier", "v' ∈ N.carrier"},
					Conclusion: "«additiveRightRelation»(u, v, v') ∈ «pairFree»",
				},
				Derive(func(b *Argument) {
					u, v, vPrime := b.FixAs[B]("u"), b.FixAs[C]("v"), b.FixAs[C]("v'")
					members := b.Assume()
					b.Show(
						"addition in N keeps the new pair in M × N, and sums and differences stay in the free module",
						By(
							group.MulIn.Read(additive),
							members,
							generatorIn.At(M, N, u, b.TermAs[C]("v + v'")),
							generatorIn.At(M, N, u, v),
							generatorIn.At(M, N, u, vPrime),
							differences,
							group.MulIn.Read(module.AddGroupOn.Read(nModule)).AsFact().At(v, vPrime)))
				}))
			scaledLeft := a.Have(
				"the scaling relation at c, u and v in the first argument lies in the free module",
				Statement{
					Binders:    "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{"c ∈ R.carrier", "u ∈ M.carrier", "v ∈ N.carrier"},
					Conclusion: "«scaledLeftRelation»(c, u, v) ∈ «pairFree»",
				},
				Derive(func(b *Argument) {
					c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"scaling in M keeps the new pair in M × N, and scaling and differences stay in the free module",
						By(
							module.SmulIn.Read(free),
							members,
							generatorIn.At(M, N, b.TermAs[B]("c • u"), v),
							generatorIn.At(M, N, u, v),
							differences,
							module.SmulIn.Read(mModule).AsFact().At(c, u)))
				}))
			scaledRight := a.Have(
				"the scaling relation at c, u and v in the second argument lies in the free module",
				Statement{
					Binders:    "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{"c ∈ R.carrier", "u ∈ M.carrier", "v ∈ N.carrier"},
					Conclusion: "«scaledRightRelation»(c, u, v) ∈ «pairFree»",
				},
				Derive(func(b *Argument) {
					c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"scaling in N keeps the new pair in M × N, and scaling and differences stay in the free module",
						By(
							module.SmulIn.Read(free),
							members,
							generatorIn.At(M, N, u, b.TermAs[C]("c • v")),
							generatorIn.At(M, N, u, v),
							differences,
							module.SmulIn.Read(nModule).AsFact().At(c, v)))
				}))
			a.Show(
				"the four kinds lie in the free module, so their span is a submodule of it",
				Simp(Fwd(tensorRelationsDef)),
				By(
					free,
					additiveLeft,
					additiveRight,
					scaledLeft,
					scaledRight,
					TensorRelationKinds.At(R, M, N, a.TermAs[Set[_PairFunction]]("«pairFree»")),
					submodule.SpanSubmodule))
		}),
})}

// TensorRelationIn — a relation element lies in the relations: the relations
// are the submodule those elements span, and a set lies in its span.
var TensorRelationIn = tensorRelationInThm{family.Add(registry.ProofEntry{
	Name: "TensorRelationIn",
	Key:  "prop_d580d17aeb908a57",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀x:(prod(B, C) → A).",
		Hypotheses: []string{"x ∈ «relationElements»"},
		Conclusion: "x ∈ tensor_relations(R, M, N)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			x *Expr[_PairFunction],
			relation Fact,
		) {
			a.Show(
				"the relations are the span of the relation elements, and a set lies in its span",
				Simp(Fwd(tensorRelationsDef)),
				BySets(
					relation,
					submodule.SubsetSpan.At(
						R,
						a.TermAs[ModuleOps[A, _PairFunction]]("«pairRecord»"),
						a.TermAs[Set[_PairFunction]]("«relationElements»"))))
		}),
})}

// TensorModuleOn — the tensor product is a module: the quotient of the
// free module on the pairs by the relations submodule.
var TensorModuleOn = tensorModuleOnThm{family.Add(registry.ProofEntry{
	Name: "TensorModuleOn",
	Key:  "prop_7535f6d065da2049",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C).",
		Hypotheses: []string{"module_on(R, N)"},
		Conclusion: "module_on(R, tensor_module(R, M, N))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
		) {
			free := a.Have(
				"the free module on M × N is an R-module",
				"module_on(R, «pairRecord»)",
				By(free_module.FreeModuleOn, module.RingOn.Read(mModule)))
			a.Show(
				"quotienting the free module by the relations submodule gives an R-module",
				Simp(Fwd(TensorModuleDef)),
				By(
					mModule,
					nModule,
					TensorRelationsSubmodule.At(R, M, N),
					submodule.QuotientModuleOn.Read(free).At(
						a.TermAs[Set[_PairFunction]]("tensor_relations(R, M, N)"))))
		}),
})}

// TensorProjectionHom — sending a function of finite support on the pairs
// to its coset of the relations is a homomorphism onto the tensor module:
// it is the quotient projection of the free module by the relations
// submodule.
var TensorProjectionHom = tensorProjectionHomThm{family.Add(registry.ProofEntry{
	Name: "TensorProjectionHom",
	Key:  "prop_c60d75faa01c9f4d",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C).",
		Hypotheses: []string{"module_on(R, N)"},
		Conclusion: "module_homomorphism(R, «pairRecord», tensor_module(R, M, N), «projection»)",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
		) {
			free := a.Have(
				"the free module on M × N is an R-module",
				"module_on(R, «pairRecord»)",
				By(free_module.FreeModuleOn, module.RingOn.Read(mModule)))
			a.Show(
				"the projection onto the quotient by a submodule is a "+
					"homomorphism, and that quotient is the tensor module",
				Simp(Fwd(TensorModuleDef)),
				By(
					mModule,
					nModule,
					TensorRelationsSubmodule.At(R, M, N),
					module_homomorphism.ProjectionHom.Read(free).At(
						a.TermAs[Set[_PairFunction]]("tensor_relations(R, M, N)"))))
		}),
})}

// TensorIsProjection — a pure tensor is the quotient projection of its
// generator: the tensor and the projection are each the generator's coset
// of the relations.
var TensorIsProjection = tensorIsProjectionThm{family.Add(registry.ProofEntry{
	Name: "TensorIsProjection",
	Key:  "prop_512785e0432476b2",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀u:B. ∀v:C.",
		Conclusion: "tensor(R, M, N, u, v) = «projection»(delta_at(R.zero, R.one, (u, v)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			u *Expr[B],
			v *Expr[C],
		) {
			a.Show(
				"either side is the coset of the generator at (u, v)",
				Simp(Fwd(TensorDef), Fwd(group.CosetMapDef)),
				Basic())
		}),
})}

// TensorRelatedCoset — two functions of finite support on the pairs
// whose difference is a relation element have one coset of the relations:
// the difference lies in the relations, a submodule, and a submodule's
// cosets of two vectors agree when their difference lies in it.
var TensorRelatedCoset = tensorRelatedCosetThm{family.Add(registry.ProofEntry{
	Name: "TensorRelatedCoset",
	Key:  "prop_5076957371ba4c01",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀x y:(prod(B, C) → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"x ∈ «pairFree»",
			"y ∈ «pairFree»",
			"fun_add(x, fun_neg(y)) ∈ «relationElements»",
		},
		Conclusion: "«projection»(x) = «projection»(y)",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			x, y *Expr[_PairFunction],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			xIn, yIn, related Fact,
		) {
			free := a.Have(
				"the free module on M × N is an R-module",
				"module_on(R, «pairRecord»)",
				By(free_module.FreeModuleOn, module.RingOn.Read(mModule)))
			a.Show(
				"the difference lies in the relations, a submodule, so x and y have one coset",
				Simp(Fwd(group.CosetMapDef)),
				By(
					related,
					TensorRelationIn.At(R, M, N, a.TermAs[_PairFunction]("fun_add(x, fun_neg(y))")),
					mModule,
					nModule,
					TensorRelationsSubmodule.At(R, M, N),
					submodule.SubmoduleCosetEq.Read(free).At(
						a.TermAs[Set[_PairFunction]]("tensor_relations(R, M, N)"),
						a.MemberOf[on.Any](x, xIn),
						a.MemberOf[on.Any](y, yIn))))
		}),
})}

// TensorRelatedSum — a function of the free module on the pairs that differs
// from a sum of two by a relation element projects to the sum of their
// projections: it has one coset with the sum, and the projection adds.
var TensorRelatedSum = tensorRelatedSumThm{family.Add(registry.ProofEntry{
	Name: "TensorRelatedSum",
	Key:  "prop_cd2e0db7aded917b",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀x y z:(prod(B, C) → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"x ∈ «pairFree»",
			"y ∈ «pairFree»",
			"z ∈ «pairFree»",
			"fun_add(z, fun_neg(fun_add(x, y))) ∈ «relationElements»",
		},
		Conclusion: "«projection»(z) = tensor_module(R, M, N).add(«projection»(x), «projection»(y))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			x, y, z *Expr[_PairFunction],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			xIn, yIn, zIn, related Fact,
		) {
			projection := a.Have(
				"the quotient projection is a module homomorphism",
				"module_homomorphism(R, «pairRecord», tensor_module(R, M, N), «projection»)",
				By(mModule, nModule, TensorProjectionHom.At(R, M, N)))
			free := module_homomorphism.HomSource.Read(projection)
			xMember, yMember := a.MemberOf[on.Any](x, xIn), a.MemberOf[on.Any](y, yIn)
			sum := group.MulIn.Read(module.AddGroupOn.Read(free)).At(xMember, yMember)
			a.Show(
				"z has the projection of x + y, and the projection adds",
				CalcEq(
					Leg(
						a.TermAs[Set[_PairFunction]]("«projection»(fun_add(x, y))"),
						"the difference is a relation element, so z and x + y have one projection",
						By(nModule, zIn, sum, related, TensorRelatedCoset.Read(mModule).At(N, z, sum))),
					FinalLeg(
						"the projection of the sum is the sum of the projections",
						By(module_homomorphism.HomAdd.Read(projection).At(xMember, yMember)))))
		}),
})}

// TensorRelatedScaled — a function of the free module on the pairs that
// differs from a scaled one by a relation element projects to the scaled
// projection: it has one coset with the scaled function, and the projection
// scales.
var TensorRelatedScaled = tensorRelatedScaledThm{family.Add(registry.ProofEntry{
	Name: "TensorRelatedScaled",
	Key:  "prop_2f3234a17fd9f100",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀s:A. ∀x z:(prod(B, C) → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"s ∈ R.carrier",
			"x ∈ «pairFree»",
			"z ∈ «pairFree»",
			"fun_add(z, fun_neg(fun_smul(s, x))) ∈ «relationElements»",
		},
		Conclusion: "«projection»(z) = tensor_module(R, M, N).smul(s, «projection»(x))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			s *Expr[A],
			x, z *Expr[_PairFunction],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			sIn, xIn, zIn, related Fact,
		) {
			projection := a.Have(
				"the quotient projection is a module homomorphism",
				"module_homomorphism(R, «pairRecord», tensor_module(R, M, N), «projection»)",
				By(mModule, nModule, TensorProjectionHom.At(R, M, N)))
			free := module_homomorphism.HomSource.Read(projection)
			scaled := a.MemberOf[on.Any](
				a.TermAs[_PairFunction]("fun_smul(s, x)"),
				GroupPremises(sIn, xIn, module.SmulIn.Read(free).AsFact().At(s, x)))
			a.Show(
				"z has the projection of s • x, and the projection scales",
				CalcEq(
					Leg(
						a.TermAs[Set[_PairFunction]]("«projection»(fun_smul(s, x))"),
						"the difference is a relation element, so z and s • x have one projection",
						By(nModule, zIn, sIn, xIn, scaled, related, TensorRelatedCoset.Read(mModule).At(N, z, scaled))),
					FinalLeg(
						"the projection of the scaled function is the scaled projection",
						By(sIn, xIn, module_homomorphism.HomSmul.Read(projection).AsFact().At(s, x)))))
		}),
})}

// TensorIn — a pure tensor of members lies in the tensor product: its
// generator lies in the free module, so its coset is one of the quotient's
// cosets.
var TensorIn = tensorInThm{family.Add(registry.ProofEntry{
	Name: "TensorIn",
	Key:  "prop_cb332ad23aeb0a34",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C). ∀u:B. ∀v:C.",
		Hypotheses: []string{"module_on(R, N)", "u ∈ M.carrier", "v ∈ N.carrier"},
		Conclusion: "tensor(R, M, N, u, v) ∈ tensor_product(R, M, N)",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			u *Member[B, on.M],
			v *Member[C, on.N],
		) {
			free := a.Have(
				"the free module on M × N is an R-module",
				"module_on(R, «pairRecord»)",
				By(free_module.FreeModuleOn, module.RingOn.Read(mModule)))
			relationsSubmodule := a.Have(
				"the relations form a submodule of the free module",
				"submodule(R, «pairRecord», tensor_relations(R, M, N))",
				By(mModule, nModule, TensorRelationsSubmodule.At(R, M, N)))
			relationSet := a.TermAs[Set[_PairFunction]]("tensor_relations(R, M, N)")
			delta := a.MemberOf[on.Any](
				a.TermAs[_PairFunction]("delta_at((u, v))"),
				GroupPremises(u, v, PairGeneratorIn.Read(module.RingOn.Read(mModule)).At(M, N, u, v)))
			a.Show(
				"the generator lies in the free module and its coset belongs to the quotient",
				Simp(Fwd(TensorDef), Fwd(TensorProductDef)),
				By(
					submodule.SubmoduleSubset.Read(relationsSubmodule),
					quotient_group.LeftCosetInLeftCosets.Read(module.AddGroupOn.Read(free)).At(relationSet, delta)))
		}),
})}

// TensorAddLeft — the tensor is additive in the first argument: a pure
// tensor is the projection of its generator, the additivity relation gives
// the generator at (u + u', v) and the sum of those at (u, v) and (u', v)
// one projection, and the projection adds.
var TensorAddLeft = tensorAddLeftThm{family.Add(registry.ProofEntry{
	Name: "TensorAddLeft",
	Key:  "prop_36ac9c0dfa08302b",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀u u':B. ∀v:C.",
		Hypotheses: []string{
			"module_on(R, N)",
			"u ∈ M.carrier",
			"u' ∈ M.carrier",
			"v ∈ N.carrier",
		},
		Conclusion: "tensor(R, M, N, u + u', v) = " +
			"tensor_module(R, M, N).add(tensor(R, M, N, u, v), tensor(R, M, N, u', v))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			u, uPrime *Member[B, on.M],
			v *Member[C, on.N],
		) {
			generatorIn := PairGeneratorIn.Read(module.RingOn.Read(mModule))
			uSum := group.MulIn.Read(module.AddGroupOn.Read(mModule)).At(u, uPrime)
			isRelation := a.Have(
				"the generator at (u + u', v) minus the sum of those "+
					"at (u, v) and (u', v) is an additivity relation",
				"«additiveLeftRelation»(u, u', v) ∈ «relationElements»",
				BySets(u, uPrime, v))
			a.Show(
				"each tensor is its generator's projection, and the relation "+
					"makes the one at (u + u', v) the sum of the other two",
				Simp(Fwd(TensorIsProjection)),
				By(
					nModule,
					u,
					uPrime,
					uSum,
					v,
					generatorIn.At(M, N, u, v),
					generatorIn.At(M, N, uPrime, v),
					generatorIn.At(M, N, uSum, v),
					isRelation,
					TensorRelatedSum.Read(mModule).At(
						N,
						a.TermAs[_PairFunction]("delta_at((u, v))"),
						a.TermAs[_PairFunction]("delta_at((u', v))"),
						a.TermAs[_PairFunction]("delta_at((u + u', v))"))))
		}),
})}

// TensorAddRight — the tensor is additive in the second argument: a pure
// tensor is the projection of its generator, the additivity relation gives
// the generator at (u, v + v') and the sum of those at (u, v) and (u, v')
// one projection, and the projection adds.
var TensorAddRight = tensorAddRightThm{family.Add(registry.ProofEntry{
	Name: "TensorAddRight",
	Key:  "prop_33e828d20fb085a4",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀u:B. ∀v v':C.",
		Hypotheses: []string{
			"module_on(R, N)",
			"u ∈ M.carrier",
			"v ∈ N.carrier",
			"v' ∈ N.carrier",
		},
		Conclusion: "tensor(R, M, N, u, v + v') = " +
			"tensor_module(R, M, N).add(tensor(R, M, N, u, v), tensor(R, M, N, u, v'))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			u *Member[B, on.M],
			v, vPrime *Member[C, on.N],
		) {
			generatorIn := PairGeneratorIn.Read(module.RingOn.Read(mModule))
			vSum := group.MulIn.Read(module.AddGroupOn.Read(nModule)).At(v, vPrime)
			isRelation := a.Have(
				"the generator at (u, v + v') minus the sum of those "+
					"at (u, v) and (u, v') is an additivity relation",
				"«additiveRightRelation»(u, v, v') ∈ «relationElements»",
				BySets(u, v, vPrime))
			a.Show(
				"each tensor is its generator's projection, and the relation "+
					"makes the one at (u, v + v') the sum of the other two",
				Simp(Fwd(TensorIsProjection)),
				By(
					nModule,
					u,
					v,
					vPrime,
					vSum,
					generatorIn.At(M, N, u, v),
					generatorIn.At(M, N, u, vPrime),
					generatorIn.At(M, N, u, vSum),
					isRelation,
					TensorRelatedSum.Read(mModule).At(
						N,
						a.TermAs[_PairFunction]("delta_at((u, v))"),
						a.TermAs[_PairFunction]("delta_at((u, v'))"),
						a.TermAs[_PairFunction]("delta_at((u, v + v'))"))))
		}),
})}

// TensorSmulLeft — a scalar on the first argument scales the tensor: a
// pure tensor is the projection of its generator, the scaling relation
// gives the generator at (c • u, v) and c times the generator at (u, v) one
// projection, and the projection scales.
var TensorSmulLeft = tensorSmulLeftThm{family.Add(registry.ProofEntry{
	Name: "TensorSmulLeft",
	Key:  "prop_5a8d146dedd60bac",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀c:A. ∀u:B. ∀v:C.",
		Hypotheses: []string{
			"module_on(R, N)",
			"c ∈ R.carrier",
			"u ∈ M.carrier",
			"v ∈ N.carrier",
		},
		Conclusion: "tensor(R, M, N, c • u, v) = tensor_module(R, M, N).smul(c, tensor(R, M, N, u, v))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			c *Member[A, on.R],
			u *Member[B, on.M],
			v *Member[C, on.N],
		) {
			generatorIn := PairGeneratorIn.Read(module.RingOn.Read(mModule))
			scaledU := module.SmulIn.Read(mModule).At(c, u)
			isRelation := a.Have(
				"the generator at (c • u, v) minus c times the one at (u, v) is a scaling relation",
				"«scaledLeftRelation»(c, u, v) ∈ «relationElements»",
				BySets(c, u, v))
			a.Show(
				"each tensor is its generator's projection, and the "+
					"relation makes the one at (c • u, v) c times the other",
				Simp(Fwd(TensorIsProjection)),
				By(
					nModule,
					c,
					u,
					scaledU,
					v,
					generatorIn.At(M, N, u, v),
					generatorIn.At(M, N, scaledU, v),
					isRelation,
					TensorRelatedScaled.Read(mModule).At(
						N,
						c,
						a.TermAs[_PairFunction]("delta_at((u, v))"),
						a.TermAs[_PairFunction]("delta_at((c • u, v))"))))
		}),
})}

// TensorSmulRightFactor — a scalar on the second argument scales the
// tensor: a pure tensor is the projection of its generator, the scaling
// relation gives the generator at (u, c • v) and c times the generator at
// (u, v) one projection, and the projection scales.
var TensorSmulRightFactor = tensorSmulRightFactorThm{family.Add(registry.ProofEntry{
	Name: "TensorSmulRightFactor",
	Key:  "prop_856b80793c36c878",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀c:A. ∀u:B. ∀v:C.",
		Hypotheses: []string{
			"module_on(R, N)",
			"c ∈ R.carrier",
			"u ∈ M.carrier",
			"v ∈ N.carrier",
		},
		Conclusion: "tensor(R, M, N, u, c • v) = tensor_module(R, M, N).smul(c, tensor(R, M, N, u, v))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			c *Member[A, on.R],
			u *Member[B, on.M],
			v *Member[C, on.N],
		) {
			generatorIn := PairGeneratorIn.Read(module.RingOn.Read(mModule))
			scaledV := module.SmulIn.Read(nModule).At(c, v)
			isRelation := a.Have(
				"the generator at (u, c • v) minus c times the one at (u, v) is a scaling relation",
				"«scaledRightRelation»(c, u, v) ∈ «relationElements»",
				BySets(c, u, v))
			a.Show(
				"each tensor is its generator's projection, and the "+
					"relation makes the one at (u, c • v) c times the other",
				Simp(Fwd(TensorIsProjection)),
				By(
					nModule,
					c,
					u,
					v,
					scaledV,
					generatorIn.At(M, N, u, v),
					generatorIn.At(M, N, u, scaledV),
					isRelation,
					TensorRelatedScaled.Read(mModule).At(
						N,
						c,
						a.TermAs[_PairFunction]("delta_at((u, v))"),
						a.TermAs[_PairFunction]("delta_at((u, c • v))"))))
		}),
})}

// TensorBalance — a scalar passes between the two arguments of a pure
// tensor: each of the two is c times u ⊗ v in the tensor module.
var TensorBalance = tensorBalanceThm{family.Add(registry.ProofEntry{
	Name: "TensorBalance",
	Key:  "prop_441d2f54b12ac0d0",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀c:A. ∀u:B. ∀v:C.",
		Hypotheses: []string{
			"module_on(R, N)",
			"c ∈ R.carrier",
			"u ∈ M.carrier",
			"v ∈ N.carrier",
		},
		Conclusion: "tensor(R, M, N, u, c • v) = tensor(R, M, N, c • u, v)",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			c *Member[A, on.R],
			u *Member[B, on.M],
			v *Member[C, on.N],
		) {
			a.Show(
				"either way the scalar comes out as c times the tensor",
				By(
					mModule,
					nModule,
					c,
					u,
					v,
					TensorSmulRightFactor.At(R, M, N, c, u, v),
					TensorSmulLeft.At(R, M, N, c, u, v)))
		}),
})}

// TensorZeroRight — a pure tensor with zero is zero: additivity makes
// it its own double, so the tensor module's additive group makes it zero.
var TensorZeroRight = tensorZeroRightThm{family.Add(registry.ProofEntry{
	Name: "TensorZeroRight",
	Key:  "prop_469a8c387f07cc04",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀u:B.",
		Hypotheses: []string{
			"module_on(R, N)",
			"u ∈ M.carrier",
		},
		Conclusion: "«zeroTensor» = tensor_relations(R, M, N)",
		Abbrev: Abbrev{
			{Name: "zeroTensor", Text: "tensor(R, M, N, u, N.zero)"},
		},
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			u *Member[B, on.M],
		) {
			// A module's additive group is read in group vocabulary: One there is
			// the module's zero, and the group product its sum.
			nAdditive := module.AddGroupOn.Read(nModule)
			zeroIn := group.OneIn.Read(nAdditive)
			zero := a.MemberOf[on.N](a.TermAs[C]("N.zero"), zeroIn)
			double := a.Have(
				"a tensor with zero is its own double",
				"tensor_module(R, M, N).add(«zeroTensor», «zeroTensor») = «zeroTensor»",
				Simp(Fwd(TensorModuleAdd)),
				By(
					mModule,
					nModule,
					u,
					zeroIn,
					group.LeftIdentityOn.Read(nAdditive).At(zero),
					TensorAddRight.At(R, M, N, u, zero, zero)))
			tensorModule := a.Have(
				"the tensor product is an R-module",
				"module_on(R, tensor_module(R, M, N))",
				By(mModule, nModule, TensorModuleOn.At(R, M, N)))
			inTensor := a.Have(
				"the pure tensor lies in the tensor module",
				"«zeroTensor» ∈ tensor_module(R, M, N).carrier",
				Simp(Fwd(TensorModuleCarrier)),
				By(mModule, nModule, u, zero, TensorIn.At(R, M, N, u, zero)))
			pureZero := a.MemberOf[on.Any](a.TermAs[Set[_PairFunction]]("«zeroTensor»"), inTensor)
			identity := a.Have(
				"an element of a group equal to its double is the identity, the tensor module's zero",
				"«zeroTensor» = tensor_module(R, M, N).zero",
				By(double, group.IdempotentIsOneOn.Read(module.AddGroupOn.Read(tensorModule)).At(pureZero)))
			a.Show(
				"the tensor module's zero is the relations, the submodule divided out",
				By(identity, TensorModuleZero.At(R, M, N)))
		}),
})}

// TensorSpan — every tensor is a finite sum of scaled pure tensors:
// expand a free-module representative on its finite support and carry
// that sum through the quotient projection.
var TensorSpan = tensorSpanThm{family.Add(registry.ProofEntry{
	Name: "TensorSpan",
	Key:  "prop_5b07809e47b1505",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀t:set(prod(B, C) → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"t ∈ tensor_product(R, M, N)",
		},
		Conclusion: "∃s:set(prod(B, C)). ∃a:(prod(B, C) → A). " +
			"    finite(s) ∧ " +
			"    s ⊆ set_cross(M.carrier, N.carrier) ∧ " +
			"    (∀q:prod(B, C). q ∈ s ⇒ a(q) ∈ R.carrier) ∧ " +
			"    t = " +
			"    module_sum(tensor_module(R, M, N).add, " +
			"        tensor_module(R, M, N).zero, " +
			"        s, " +
			"        λq:prod(B, C). tensor_module(R, M, N).smul(a(q), tensor(R, M, N, fst(q), snd(q))))",
		Abbrev: Abbrev{
			{Name: "scaledTerms", Text: "λq:prod(B, C). fun_smul⟨D:prod(B, C)⟩(R.mul, f(q), delta_at(q))"},
			{Name: "projectedTerms", Text: "λq:prod(B, C). «projection»(«scaledTerms»(q))"},
			{Name: "tensorTerms", Text: "λq:prod(B, C). " +
				"    tensor_module(R, M, N).smul(f(q), tensor(R, M, N, fst(q), snd(q)))"},
			{Name: "freeExpansion", Text: "module_sum(fun_add⟨D:prod(B, C)⟩(R.add), " +
				"    fun_zero⟨D:prod(B, C)⟩(R.zero), " +
				"    fun_support(R.zero, f), " +
				"    «scaledTerms»)"},
			{Name: "projectedSum", Text: "module_sum(tensor_module(R, M, N).add, " +
				"    tensor_module(R, M, N).zero, " +
				"    fun_support(R.zero, f), " +
				"    «projectedTerms»)"},
		},
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			t *Expr[Set[_PairFunction]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			tIn Fact,
		) {
			ring := module.RingOn.Read(mModule)
			pairsOf := a.TermAs[Set[Prod[B, C]]]("set_cross(M.carrier, N.carrier)")
			relationSet := a.TermAs[Set[_PairFunction]]("tensor_relations(R, M, N)")
			free := a.Have(
				"the free module on M × N is an R-module",
				"module_on(R, «pairRecord»)",
				By(free_module.FreeModuleOn, ring))
			relationsSubmodule := a.Have(
				"the relations form a submodule of the free module",
				"submodule(R, «pairRecord», tensor_relations(R, M, N))",
				By(mModule, nModule, TensorRelationsSubmodule.At(R, M, N)))
			f, representative := a.ObtainAs[_PairFunction](
				"t is the coset of a function of finite support on M × N",
				"∃f:(prod(B, C) → A). "+
					"    t = left_coset(fun_add(R.add), f, tensor_relations(R, M, N)) ∧ f ∈ «pairFree»",
				By(
					submodule.SubmoduleSubset.Read(relationsSubmodule),
					tIn,
					TensorProductDef.At(R, M, N),
					quotient_group.InLeftCosets.Read(module.AddGroupOn.Read(free)).At(relationSet, t)))
			repParts := a.Conjuncts(
				representative,
				"t is the coset of f",
				"f lies in the free module")
			tIsCoset, fIn := repParts[0], repParts[1]
			support := a.TermAs[Set[Prod[B, C]]]("fun_support(R.zero, f)")
			supportData := a.Have(
				"f has finite support inside M × N and takes its values in R",
				"finite(fun_support(R.zero, f)) ∧ "+
					"fun_support(R.zero, f) ⊆ set_cross(M.carrier, N.carrier) ∧ "+
					"(∀q:prod(B, C). f(q) ∈ R.carrier)",
				By(
					fIn,
					function_module.FiniteSuppMember.At(
						a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier"), pairsOf, f)))
			supportParts := a.Conjuncts(
				supportData,
				"the support is finite",
				"the support lies in M × N",
				"all coefficients lie in R")
			finite, inPairs, values := supportParts[0], supportParts[1], supportParts[2]
			projection := a.Have(
				"the quotient projection is a module homomorphism",
				"module_homomorphism(R, «pairRecord», tensor_module(R, M, N), «projection»)",
				By(mModule, nModule, TensorProjectionHom.At(R, M, N)))
			scaledTerms := a.TermAs[Fun[Prod[B, C], _PairFunction]]("«scaledTerms»")
			termsIn := a.Have(
				"each scaled generator in the expansion lies in the free module",
				"∀q:prod(B, C). q ∈ fun_support(R.zero, f) ⇒ «scaledTerms»(q) ∈ «pairFree»",
				Derive(func(b *Argument) {
					q := b.FixAs[Prod[B, C]]("q")
					qIn := b.Assume()
					b.Show(
						"the coefficient lies in R and the generator is based at a pair of M × N",
						BySets(
							qIn,
							inPairs,
							values.At(q),
							free_module.DeltaAtIn.Read(ring).At(pairsOf, q),
							module.SmulIn.Read(free).AsFact().At(b.TermAs[A]("f(q)"), b.TermAs[_PairFunction]("delta_at(q)"))))
				}))
			termImage := a.Have(
				"the projection of each scaled generator is the corresponding scaled pure tensor",
				"∀q:prod(B, C). q ∈ fun_support(R.zero, f) ⇒ «projectedTerms»(q) = «tensorTerms»(q)",
				Derive(func(b *Argument) {
					q := b.FixAs[Prod[B, C]]("q")
					qIn := b.Assume()
					scalingGuards := b.Have(
						"the coefficient lies in R and the generator in the free module",
						"f(q) ∈ R.carrier ∧ delta_at(q) ∈ «pairFree»",
						BySets(qIn, inPairs, values.At(q), free_module.DeltaAtIn.Read(ring).At(pairsOf, q)))
					b.Show(
						"the projection scales, and q, the pair of its projections, "+
							"has the pure tensor as its generator's projection",
						Simp(Fwd(TensorIsProjection), Fwd(pairs.PairEta)),
						By(
							scalingGuards,
							module_homomorphism.HomSmul.Read(projection).AsFact().At(
								b.TermAs[A]("f(q)"),
								b.TermAs[_PairFunction]("delta_at(q)"))))
				}))

			a.Take(support)
			a.Take(f)
			a.Show(
				"the support and coefficients give the required finite tensor expansion",
				SplitConjAll(
					Case(
						"the support is finite",
						By(finite)),
					Case(
						"every supporting pair lies in M × N",
						By(inPairs)),
					Case(
						"each coefficient lies in R",
						By(values)),
					Case(
						"project the free-module expansion term by term",
						CalcEq(
							Leg(
								a.TermAs[Set[_PairFunction]]("«projection»(f)"),
								"t is the projection of its representative",
								Simp(Fwd(group.CosetMapDef)),
								By(tIsCoset)),
							Leg(
								a.TermAs[Set[_PairFunction]]("«projection»(«freeExpansion»)"),
								"expand f on its finite support",
								By(fIn, free_module.FreeModuleExpand.Read(ring).At(pairsOf, f))),
							Leg(
								a.TermAs[Set[_PairFunction]]("«projectedSum»"),
								"the projection preserves this finite sum",
								By(finite, termsIn, module_homomorphism.HomSum.Read(projection).At(support, scaledTerms))),
							FinalLeg(
								"each projected summand is its scaled pure tensor",
								By(termImage, module.ModuleSumCongruence))))))
		}),
})}

// PureTensorsSpan — the pure tensors span the tensor module: their span
// is a submodule of it, and it holds every tensor, a finite sum of scaled
// pure tensors.
var PureTensorsSpan = pureTensorsSpanThm{family.Add(registry.ProofEntry{
	Name: "PureTensorsSpan",
	Key:  "prop_c1dfd7536ce0500e",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C).",
		Hypotheses: []string{"module_on(R, N)"},
		Conclusion: "module_span(R, tensor_module(R, M, N), «pureTensors») = " +
			"tensor_module(R, M, N).carrier",
		Abbrev: Abbrev{
			{Name: "span", Text: "module_span(R, tensor_module(R, M, N), «pureTensors»)"},
			{Name: "scaledTensors", Text: "λq:prod(B, C). " +
				"    tensor_module(R, M, N).smul(coeff(q), tensor(R, M, N, fst(q), snd(q)))"},
		},
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
		) {
			tensors := a.TermAs[ModuleOps[A, Set[_PairFunction]]]("tensor_module(R, M, N)")
			pureTensors := a.TermAs[Set[Set[_PairFunction]]]("«pureTensors»")
			span := a.TermAs[Set[Set[_PairFunction]]]("«span»")
			mCarrier, nCarrier := a.TermAs[Set[B]]("M.carrier"), a.TermAs[Set[C]]("N.carrier")
			tensorModule := a.Have(
				"the tensor product is an R-module",
				"module_on(R, tensor_module(R, M, N))",
				By(mModule, nModule, TensorModuleOn.At(R, M, N)))
			pureIn := a.Have(
				"the pure tensors lie in the tensor module",
				"«pureTensors» ⊆ tensor_module(R, M, N).carrier",
				Simp(Fwd(TensorModuleCarrier)),
				BySets(nModule, TensorIn.Read(mModule).AsFact().At(N)))
			spanned := a.Have(
				"their span is a submodule of the tensor module",
				"submodule(R, tensor_module(R, M, N), «span»)",
				By(pureIn, submodule.SpanSubmodule.Read(tensorModule).At(pureTensors)))
			pureInSpan := a.Have(
				"a pure tensor of members lies in the span",
				"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ tensor(R, M, N, u, v) ∈ «span»",
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					b.FixAs[C]("v")
					members := b.Assume()
					pure := b.Have(
						"it is one of the pure tensors",
						"tensor(R, M, N, u, v) ∈ «pureTensors»",
						By(members))
					b.Show(
						"and a set lies in its span",
						BySets(pure, submodule.SubsetSpan.At(R, tensors, pureTensors)))
				}))
			holdsTensors := a.Have(
				"the span holds every tensor",
				"tensor_module(R, M, N).carrier ⊆ «span»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					t := b.FixAs[Set[_PairFunction]]("t")
					inTensors := b.Simplified(b.Assume(), Rev(TensorProductDef))
					s, _, spanData := b.Unpack2As[Set[Prod[B, C]], _PairFunction](
						GroupPremises(mModule, nModule, inTensors, TensorSpan.At(R, M, N, t)), "s", "coeff")
					spanParts := b.Conjuncts(
						spanData,
						"the supporting set is finite",
						"its points lie in M × N",
						"its coefficients lie in R",
						"its scaled pure tensors sum to t")
					finite, inPairs, coefficients, expansion := spanParts[0], spanParts[1], spanParts[2], spanParts[3]
					summands := b.TermAs[Fun[Prod[B, C], Set[_PairFunction]]]("«scaledTensors»")
					termsIn := b.Have(
						"each scaled pure tensor of the expansion lies in the span",
						"∀q:prod(B, C). q ∈ s ⇒ «scaledTensors»(q) ∈ «span»",
						Derive(func(c *Argument) {
							q := c.FixAs[Prod[B, C]]("q")
							qIn := c.Assume()
							components := c.Have(
								"the components of q lie in M and in N",
								"fst(q) ∈ M.carrier ∧ snd(q) ∈ N.carrier",
								BySets(qIn, inPairs, set_product.InCrossProjections.At(mCarrier, nCarrier, q)))
							c.Show(
								"the span is closed under scaling by the coefficient at q",
								By(
									submodule.SubmoduleSmul.Read(spanned),
									qIn,
									coefficients.At(q),
									components,
									pureInSpan.At(c.TermAs[B]("fst(q)"), c.TermAs[C]("snd(q)"))))
						}))
					b.Show(
						"t is a finite sum of vectors of the span, a submodule",
						Simp(Fwd(expansion)),
						By(finite, termsIn, spanned, submodule.SubmoduleModuleSum.Read(tensorModule).At(span, s, summands)))
				}))
			a.Show(
				"the span lies in the tensor module and holds every tensor",
				By(
					submodule.SubmoduleSubset.Read(spanned),
					holdsTensors,
					set_order.SubsetAntisym.At(
						span, a.TermAs[Set[Set[_PairFunction]]]("tensor_module(R, M, N).carrier"))))
		}),
})}

// TensorInduction — a submodule of M ⊗ N that holds every pure tensor
// u ⊗ v of a member u of M and a member v of N is all of M ⊗ N: the pure
// tensors span the tensor module (PureTensorsSpan above), and a
// submodule holding a set holds its span.
var TensorInduction = tensorInductionThm{family.Add(registry.ProofEntry{
	Name: "TensorInduction",
	Key:  "prop_aabd59c946c75f",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀S:set(set(prod(B, C) → A)).",
		Hypotheses: []string{
			"module_on(R, N)",
			"submodule(R, tensor_module(R, M, N), S)",
			"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ tensor(R, M, N, u, v) ∈ S",
		},
		Conclusion: "tensor_module(R, M, N).carrier ⊆ S",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			S *Expr[Set[Set[_PairFunction]]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			sub, pureIn Fact,
		) {
			spanned := a.Have(
				"the pure tensors span M ⊗ N",
				"module_span(R, tensor_module(R, M, N), «pureTensors») = tensor_module(R, M, N).carrier",
				By(mModule, nModule, PureTensorsSpan.At(R, M, N)))
			generatorsIn := a.Have(
				"S holds the spanning set",
				"«pureTensors» ⊆ S",
				BySets(pureIn))
			a.Show(
				"a submodule holding the spanning set holds its span",
				Simp(Rev(spanned)),
				By(
					sub,
					generatorsIn,
					submodule.SpanLeast.At(
						R,
						a.TermAs[ModuleOps[A, Set[_PairFunction]]]("tensor_module(R, M, N)"),
						a.TermAs[Set[Set[_PairFunction]]]("«pureTensors»"),
						S)))
		}),
})}

// BilinearLift — a bilinear map phi : M × N → L, read on the pairs, extends to
// a homomorphism out of the free module on them, sending the generator at
// (u, v) to phi(u, v): phi takes the pairs into L, and a map of a set into a
// module extends to the free module on the set.
var BilinearLift = bilinearLiftThm{family.Add(registry.ProofEntry{
	Name: "BilinearLift",
	Key:  "prop_5a0c5bb98c79bcfe",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C). ∀L:module_ops(A, D). ∀phi:(B → C → D).",
		Hypotheses: []string{"bilinear_map(R, M, N, L, phi)"},
		Conclusion: "module_homomorphism(R, «pairRecord», L, «bilinearLift») ∧ " +
			"(∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ «bilinearLift»(delta_at((u, v))) = phi(u, v))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			phi *Arrow2[B, C, D],
			mModule module.ModuleFact[on.R, on.M],
			bilinear Fact,
		) {
			clauses := a.Conjuncts(
				GroupPremises(bilinear, module_homomorphism.BilinearMapClauses.Read(mModule).At(N, L, phi)),
				"N is a module",
				"L is a module",
				"phi takes the pairs of M × N into L",
				"phi is additive in its first argument",
				"and in its second",
				"a scalar on the first argument comes out of phi",
				"and so does one on the second")
			lModule, phiIn := clauses[1], clauses[2]
			mCarrier, nCarrier := a.TermAs[Set[B]]("M.carrier"), a.TermAs[Set[C]]("N.carrier")
			pairsOf := a.TermAs[Set[Prod[B, C]]]("set_cross(M.carrier, N.carrier)")
			onPairs := a.TermAs[Fun[Prod[B, C], D]]("λp:prod(B, C). phi(fst(p), snd(p))")
			phiOnPairs := a.Have(
				"phi read on a pair of M × N lies in L",
				"∀p:prod(B, C). p ∈ set_cross(M.carrier, N.carrier) ⇒ phi(fst(p), snd(p)) ∈ L.carrier",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[B, C]]("p")
					b.Show(
						"a pair of M × N has its projections in M and in N",
						By(
							phiIn.At(b.TermAs[B]("fst(p)"), b.TermAs[C]("snd(p)")),
							set_product.InCrossProjections.At(mCarrier, nCarrier, p)))
				}))
			hom := a.Have(
				"phi read on the generators extends to a homomorphism out of the free module",
				"module_homomorphism(R, «pairRecord», L, «bilinearLift»)",
				By(free_module.FreeLiftHom.Read(lModule), phiOnPairs))
			generatorValue := a.Have(
				"the lift sends the generator at a pair to phi of the pair",
				"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ «bilinearLift»(delta_at((u, v))) = phi(u, v)",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					v := b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"the lift returns phi read on the pairs at a generator, and a pair's projections are its parts",
						CalcEq(
							Leg(
								b.TermAs[D]("phi(fst((u, v)), snd((u, v)))"),
								"the lift returns phi read on the pairs at the generator at (u, v)",
								By(
									members,
									phiOnPairs,
									set_product.InCross.At(mCarrier, nCarrier, u, v),
									free_module.FreeLiftDelta.Read(lModule).At(pairsOf, onPairs, b.TermAs[Prod[B, C]]("(u, v)")))),
							FinalLeg(
								"fst((u, v)) is u and snd((u, v)) is v",
								Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
								Basic()),
						))
				}))
			a.Show(
				"the lift is that homomorphism, with those values on the generators",
				By(hom, generatorValue))
		}),
})}

// BilinearLiftKillsRelations — the lift of a bilinear map to the free module on
// the pairs kills the relations: written out, its value at a relation element
// of each kind is a combination in L that bilinearity makes zero, and the
// kernel is a submodule, so it holds the submodule those elements span.
var BilinearLiftKillsRelations = bilinearLiftKillsRelationsThm{family.Add(registry.ProofEntry{
	Name: "BilinearLiftKillsRelations",
	Key:  "prop_5c352ce09603ee3c",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C). ∀L:module_ops(A, D). ∀phi:(B → C → D).",
		Hypotheses: []string{"bilinear_map(R, M, N, L, phi)"},
		Conclusion: "tensor_relations(R, M, N) ⊆ «kernel»",
		Abbrev: Abbrev{
			{Name: "kernel", Text: "group_kernel(L.zero, «pairFree», «bilinearLift»)"},
		},
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			phi *Arrow2[B, C, D],
			mModule module.ModuleFact[on.R, on.M],
			bilinear Fact,
		) {
			clauses := a.Conjuncts(
				GroupPremises(bilinear, module_homomorphism.BilinearMapClauses.Read(mModule).At(N, L, phi)),
				"N is a module",
				"L is a module",
				"phi takes the pairs of M × N into L",
				"phi is additive in its first argument",
				"and in its second",
				"a scalar on the first argument comes out of phi",
				"and so does one on the second")
			nModule := clauses[0]
			addLeft, addRight, smulLeft, smulRight := clauses[3], clauses[4], clauses[5], clauses[6]
			lift := a.Conjuncts(
				GroupPremises(bilinear, BilinearLift.Read(mModule).At(N, L, phi)),
				"the lift is a homomorphism out of the free module",
				"it sends the generator at a pair to phi of the pair")
			hom, generatorValue := lift[0], lift[1]
			generatorIn := PairGeneratorIn.Read(module.RingOn.Read(mModule))
			additiveLeft := a.Have(
				"the lift of the additivity relation at u, u' of M and v "+
					"of N is phi(u + u', v) minus phi(u, v) + phi(u', v), zero",
				Statement{
					Binders:    "∀u u':B. ∀v:C.",
					Hypotheses: []string{"u ∈ M.carrier", "u' ∈ M.carrier", "v ∈ N.carrier"},
					Conclusion: "«additiveLeftRelation»(u, u', v) ∈ «kernel»",
				},
				Derive(func(b *Argument) {
					u, uPrime, v := b.FixAs[B]("u"), b.FixAs[B]("u'"), b.FixAs[C]("v")
					members := b.Assume()
					sum := b.TermAs[B]("u + u'")
					b.Show(
						"the combination vanishes in L, phi being additive in its first argument",
						ByChase(
							Depth(0),
							hom,
							members,
							generatorIn.At(M, N, sum, v),
							generatorIn.At(M, N, u, v),
							generatorIn.At(M, N, uPrime, v),
							generatorValue.At(sum, v),
							generatorValue.At(u, v),
							generatorValue.At(uPrime, v),
							addLeft.At(u, uPrime, v),
							group.MulIn.Read(module.AddGroupOn.Read(mModule)).AsFact().At(u, uPrime)))
				}))
			additiveRight := a.Have(
				"the lift of the additivity relation at u of M and v, v' "+
					"of N is phi(u, v + v') minus phi(u, v) + phi(u, v'), zero",
				Statement{
					Binders:    "∀u:B. ∀v v':C.",
					Hypotheses: []string{"u ∈ M.carrier", "v ∈ N.carrier", "v' ∈ N.carrier"},
					Conclusion: "«additiveRightRelation»(u, v, v') ∈ «kernel»",
				},
				Derive(func(b *Argument) {
					u, v, vPrime := b.FixAs[B]("u"), b.FixAs[C]("v"), b.FixAs[C]("v'")
					members := b.Assume()
					sum := b.TermAs[C]("v + v'")
					b.Show(
						"the combination vanishes in L, phi being additive in its second argument",
						ByChase(
							Depth(0),
							hom,
							members,
							generatorIn.At(M, N, u, sum),
							generatorIn.At(M, N, u, v),
							generatorIn.At(M, N, u, vPrime),
							generatorValue.At(u, sum),
							generatorValue.At(u, v),
							generatorValue.At(u, vPrime),
							addRight.At(u, v, vPrime),
							group.MulIn.Read(module.AddGroupOn.Read(nModule)).AsFact().At(v, vPrime)))
				}))
			scaledLeft := a.Have(
				"the lift of the scaling relation at c, u of M and "+
					"v of N is phi(c • u, v) minus c • phi(u, v), zero",
				Statement{
					Binders:    "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{"c ∈ R.carrier", "u ∈ M.carrier", "v ∈ N.carrier"},
					Conclusion: "«scaledLeftRelation»(c, u, v) ∈ «kernel»",
				},
				Derive(func(b *Argument) {
					c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
					members := b.Assume()
					scaled := b.TermAs[B]("c • u")
					b.Show(
						"the combination vanishes in L, a scalar on the first argument coming out of phi",
						ByChase(
							Depth(0),
							hom,
							members,
							generatorIn.At(M, N, scaled, v),
							generatorIn.At(M, N, u, v),
							generatorValue.At(scaled, v),
							generatorValue.At(u, v),
							smulLeft.At(c, u, v),
							module.SmulIn.Read(mModule).AsFact().At(c, u)))
				}))
			scaledRight := a.Have(
				"the lift of the scaling relation at c, u of M and "+
					"v of N is phi(u, c • v) minus c • phi(u, v), zero",
				Statement{
					Binders:    "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{"c ∈ R.carrier", "u ∈ M.carrier", "v ∈ N.carrier"},
					Conclusion: "«scaledRightRelation»(c, u, v) ∈ «kernel»",
				},
				Derive(func(b *Argument) {
					c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
					members := b.Assume()
					scaled := b.TermAs[C]("c • v")
					b.Show(
						"the combination vanishes in L, a scalar on the second argument coming out of phi",
						ByChase(
							Depth(0),
							hom,
							members,
							generatorIn.At(M, N, u, scaled),
							generatorIn.At(M, N, u, v),
							generatorValue.At(u, scaled),
							generatorValue.At(u, v),
							smulRight.At(c, u, v),
							module.SmulIn.Read(nModule).AsFact().At(c, v)))
				}))
			record := a.TermAs[ModuleOps[A, _PairFunction]]("«pairRecord»")
			kernel := a.TermAs[Set[_PairFunction]]("«kernel»")
			a.Show(
				"the kernel, a submodule, holds the four kinds and so the relations they span",
				Simp(Fwd(tensorRelationsDef)),
				By(
					hom,
					module_homomorphism.KernelSubmodule.At(
						R, record, L, a.TermAs[Fun[_PairFunction, D]]("«bilinearLift»")),
					additiveLeft,
					additiveRight,
					scaledLeft,
					scaledRight,
					TensorRelationKinds.At(R, M, N, kernel),
					submodule.SpanLeast.At(R, record, a.TermAs[Set[_PairFunction]]("«relationElements»"), kernel)))
		}),
})}

// TensorUniversal — a bilinear map phi : M × N → L factors through the
// tensor product: its lift out of the free module on the pairs kills the
// relations, so it descends to the quotient by them, the tensor product, as a
// homomorphism taking the lift's value on each coset, and on u ⊗ v, the coset
// of the generator at (u, v), that value is phi(u, v).
var TensorUniversal = tensorUniversalThm{family.Add(registry.ProofEntry{
	Name: "TensorUniversal",
	Key:  "prop_1cf04b65babcde39",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C). ∀L:module_ops(A, D). ∀phi:(B → C → D).",
		Hypotheses: []string{"bilinear_map(R, M, N, L, phi)"},
		Conclusion: "∃h:(set(prod(B, C) → A) → D). " +
			"    module_homomorphism(R, tensor_module(R, M, N), L, h) ∧ " +
			"    (∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ h(tensor(R, M, N, u, v)) = phi(u, v))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			phi *Arrow2[B, C, D],
			mModule module.ModuleFact[on.R, on.M],
			bilinear Fact,
		) {
			lift := a.Conjuncts(
				GroupPremises(bilinear, BilinearLift.Read(mModule).At(N, L, phi)),
				"the lift of phi is a homomorphism out of the free module",
				"it sends the generator at a pair to phi of the pair")
			hom, generatorValue := lift[0], lift[1]
			relationsInKernel := a.Have(
				"the lift kills the relations",
				"tensor_relations(R, M, N) ⊆ group_kernel(L.zero, «pairFree», «bilinearLift»)",
				By(bilinear, BilinearLiftKillsRelations.Read(mModule).At(N, L, phi)))
			relationsSubmodule := a.Have(
				"the relations are a submodule of the free module",
				"submodule(R, «pairRecord», tensor_relations(R, M, N))",
				By(
					bilinear,
					module_homomorphism.BilinearMapClauses.Read(mModule).At(N, L, phi),
					TensorRelationsSubmodule.Read(mModule)))
			factor := module_homomorphism.InducedMapHom.At(
				R,
				a.TermAs[ModuleOps[A, _PairFunction]]("«pairRecord»"),
				L,
				a.TermAs[Set[_PairFunction]]("tensor_relations(R, M, N)"),
				a.TermAs[Fun[_PairFunction, D]]("«bilinearLift»"))
			linear := a.Have(
				"so the lift descends to a homomorphism out of the quotient by the relations, the tensor product",
				"module_homomorphism(R, tensor_module(R, M, N), L, induced_map(«bilinearLift»))",
				Simp(Fwd(TensorModuleDef)),
				By(factor, relationsSubmodule, hom, relationsInKernel))
			value := a.Have(
				"and the induced map takes the lift's value at x on the coset of x",
				Statement{
					Binders: "∀x:(prod(B, C) → A).",
					Hypotheses: []string{
						"x ∈ «pairFree»",
					},
					Conclusion: "induced_map(«bilinearLift», " +
						"    left_coset(fun_add(R.add), x, tensor_relations(R, M, N))) = " +
						"«bilinearLift»(x)",
				},
				By(factor, relationsSubmodule, hom, relationsInKernel))
			generatorIn := PairGeneratorIn.Read(module.RingOn.Read(mModule))
			onTensors := a.Have(
				"so the induced map sends u ⊗ v to phi(u, v)",
				Statement{
					Binders: "∀u:B. ∀v:C.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ N.carrier",
					},
					Conclusion: "induced_map(«bilinearLift», tensor(R, M, N, u, v)) = phi(u, v)",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					v := b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"u ⊗ v is the coset of the generator at (u, v), where "+
							"the induced map takes the lift's value, phi(u, v)",
						Simp(Fwd(TensorDef)),
						By(
							members,
							generatorIn.At(M, N, u, v),
							value.At(b.TermAs[_PairFunction]("delta_at((u, v))")),
							generatorValue.At(u, v)))
				}))
			a.Take(a.TermAs[Fun[Set[_PairFunction], D]]("induced_map(«bilinearLift»)"))
			a.Show(
				"the induced map is the homomorphism the bilinear map factors through",
				By(linear, onTensors))
		}),
})}

// TensorLinearBilinear — a linear map h out of M ⊗ N, read on the pure
// tensors, is bilinear: (u, v) ↦ h(u ⊗ v) is additive and homogeneous in
// each argument, since the tensor is and h is linear. It is the converse
// of TensorUniversal above.
var TensorLinearBilinear = tensorLinearBilinearThm{family.Add(registry.ProofEntry{
	Name: "TensorLinearBilinear",
	Key:  "prop_67a0e4ac551e6abc",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀L:module_ops(A, D). ∀h:(set(prod(B, C) → A) → D).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_homomorphism(R, tensor_module(R, M, N), L, h)",
		},
		Conclusion: "bilinear_map(R, M, N, L, «paired»)",
		Abbrev: Abbrev{
			{Name: "paired", Text: "λu:B. λv:C. h(tensor(R, M, N, u, v))"},
		},
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			h *Arrow[Set[_PairFunction], D],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			hHom Fact,
		) {
			clauses := a.Have(
				"the tensor laws and linearity of h give the bilinear clauses",
				"(∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ «paired»(u, v) ∈ L.carrier) ∧ "+
					"(∀u u':B. ∀v:C. "+
					"    u ∈ M.carrier ∧ u' ∈ M.carrier ∧ v ∈ N.carrier ⇒ "+
					"    «paired»(M.add(u, u'), v) = L.add(«paired»(u, v), «paired»(u', v))) ∧ "+
					"(∀u:B. ∀v v':C. "+
					"    u ∈ M.carrier ∧ v ∈ N.carrier ∧ v' ∈ N.carrier ⇒ "+
					"    «paired»(u, N.add(v, v')) = L.add(«paired»(u, v), «paired»(u, v'))) ∧ "+
					"(∀c:A. ∀u:B. ∀v:C. "+
					"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ "+
					"    «paired»(M.smul(c, u), v) = L.smul(c, «paired»(u, v))) ∧ "+
					"(∀c:A. ∀u:B. ∀v:C. "+
					"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ "+
					"    «paired»(u, N.smul(c, v)) = L.smul(c, «paired»(u, v)))",
				SplitConjAll(
					Case(
						"h sends a pure tensor into L",
						By(
							mModule,
							nModule,
							At(TensorIn, R, M, N),
							TensorModuleCarrier.At(R, M, N),
							module_homomorphism.HomIn.Read(hHom))),
					Case(
						"h preserves the sum obtained by adding first factors",
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							uPrime := b.FixAs[B]("u'")
							v := b.FixAs[C]("v")
							members := b.Assume()
							uv := b.TermAs[Set[_PairFunction]]("tensor(R, M, N, u, v)")
							uPrimeV := b.TermAs[Set[_PairFunction]]("tensor(R, M, N, u', v)")
							b.Show(
								"the tensor sum law followed by h's additivity gives the first sum law",
								By(
									mModule,
									nModule,
									members,
									TensorIn.At(R, M, N, u, v),
									TensorIn.At(R, M, N, uPrime, v),
									TensorModuleCarrier.At(R, M, N),
									TensorAddLeft.At(R, M, N, u, uPrime, v),
									At(module_homomorphism.HomAdd.Read(hHom), uv, uPrimeV)))
						})),
					Case(
						"h preserves the sum obtained by adding second factors",
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							v := b.FixAs[C]("v")
							vPrime := b.FixAs[C]("v'")
							members := b.Assume()
							uv := b.TermAs[Set[_PairFunction]]("tensor(R, M, N, u, v)")
							uvPrime := b.TermAs[Set[_PairFunction]]("tensor(R, M, N, u, v')")
							b.Show(
								"the tensor sum law followed by h's additivity gives the second sum law",
								By(
									mModule,
									nModule,
									members,
									TensorIn.At(R, M, N, u, v),
									TensorIn.At(R, M, N, u, vPrime),
									TensorModuleCarrier.At(R, M, N),
									TensorAddRight.At(R, M, N, u, v, vPrime),
									At(module_homomorphism.HomAdd.Read(hHom), uv, uvPrime)))
						})),
					Case(
						"a scalar on the first factor comes through the tensor and h",
						By(
							mModule,
							nModule,
							At(TensorIn, R, M, N),
							TensorModuleCarrier.At(R, M, N),
							At(TensorSmulLeft, R, M, N),
							module_homomorphism.HomSmul.Read(hHom))),
					Case(
						"a scalar on the second factor comes through the tensor and h",
						By(
							mModule,
							nModule,
							At(TensorIn, R, M, N),
							TensorModuleCarrier.At(R, M, N),
							At(TensorSmulRightFactor, R, M, N),
							module_homomorphism.HomSmul.Read(hHom)))))
			a.Show(
				"the pairing followed by h is bilinear",
				By(
					mModule,
					nModule,
					module_homomorphism.HomTarget.Read(hHom),
					clauses,
					module_homomorphism.BilinearMapOfClauses.At(R, M, N, L, a.TermAs[Fun2[B, C, D]]("«paired»"))))
		}),
})}

// TensorUniversalUnique — two homomorphisms out of the tensor product
// agreeing on the pure tensors agree: homomorphisms agreeing on a set agree
// on its span, and the pure tensors span the tensor module.
var TensorUniversalUnique = tensorUniversalUniqueThm{family.Add(registry.ProofEntry{
	Name: "TensorUniversalUnique",
	Key:  "prop_b065883ecaa1b7af",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀h h':(set(prod(B, C) → A) → D). " +
			"∀t:set(prod(B, C) → A).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_homomorphism(R, tensor_module(R, M, N), L, h)",
			"module_homomorphism(R, tensor_module(R, M, N), L, h')",
			"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ h(tensor(R, M, N, u, v)) = h'(tensor(R, M, N, u, v))",
			"t ∈ tensor_product(R, M, N)",
		},
		Conclusion: "h(t) = h'(t)",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			h, hPrime *Expr[Fun[Set[_PairFunction], D]],
			t *Expr[Set[_PairFunction]],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			hHom, hPrimeHom, agree, tIn Fact,
		) {
			pureIn := a.Have(
				"the pure tensors lie in the tensor module",
				"«pureTensors» ⊆ tensor_module(R, M, N).carrier",
				Simp(Fwd(TensorModuleCarrier)),
				BySets(nModule, TensorIn.Read(mModule).AsFact().At(N)))
			agreeOnPure := a.Have(
				"the two homomorphisms agree on the pure tensors",
				"∀x:set(prod(B, C) → A). x ∈ «pureTensors» ⇒ h(x) = h'(x)",
				By(agree))
			inSpan := a.Have(
				"t lies in the span of the pure tensors, which is the tensor module",
				"t ∈ module_span(R, tensor_module(R, M, N), «pureTensors»)",
				By(tIn, TensorModuleCarrier.At(R, M, N), mModule, nModule, PureTensorsSpan.At(R, M, N)))
			a.Show(
				"homomorphisms agreeing on a set agree on its span",
				By(
					hHom,
					hPrimeHom,
					pureIn,
					agreeOnPure,
					inSpan,
					linear_independence.HomAgreeOnSpan.At(
						R,
						a.TermAs[ModuleOps[A, Set[_PairFunction]]]("tensor_module(R, M, N)"),
						L,
						h,
						hPrime,
						a.TermAs[Set[Set[_PairFunction]]]("«pureTensors»"),
						t)))
		}),
})}

// TensorRegular — tensoring with the ring itself changes nothing: u ⊗ r
// ↦ r • u is an isomorphism M ⊗ R → M.
var TensorRegular = tensorRegularThm{family.Add(registry.ProofEntry{
	Name: "TensorRegular",
	Key:  "prop_c05ac7bf4329cf1",
	Deps: []registry.EntryLike{
		TensorUniversal,
		TensorSpan,
		TensorSmulLeft,
		TensorBalance,
		TensorModuleOn,
		module.SmulOne,
	},
	Build: family.Card(
		module.ModuleOn.Statement(
			"∃h:(set(prod(B, A) → A) → B). "+
				"    module_isomorphism(R, tensor_module(R, M, regular_module(R)), M, h) ∧ "+
				"    (∀u:B. ∀r:A. "+
				"        u ∈ M.carrier ∧ r ∈ R.carrier ⇒ h(tensor(R, M, regular_module(R), u, r)) = r • u)"),
		"(u, r) ↦ r • u is bilinear, so TensorUniversal gives h; u ↦ u ⊗ R.one is linear and inverse to "+
			"it on pure tensors, since u ⊗ r = (r • u) ⊗ R.one (TensorBalance), and these span (TensorSpan)"),
})}

// TensorBasisSeparates — a basis of V separates the terms of a tensor: a
// sum of tensors u ⊗ x(u), u running over a part of the basis, vanishes only
// when every x(u) does. The contraction along the coordinate at d keeps the
// term at d alone.
var TensorBasisSeparates = tensorBasisSeparatesThm{family.Add(registry.ProofEntry{
	Name: "TensorBasisSeparates",
	Key:  "prop_92efcb1b851e3fa9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀E T:set(B). " +
			"∀x:(B → C). " +
			"∀d:B.",
		Hypotheses: []string{
			"module_on(R, V)",
			"module_on(R, W)",
			"finite(E)",
			"module_basis(R, V, E)",
			"T ⊆ E",
			"∀u:B. u ∈ T ⇒ x(u) ∈ W.carrier",
			"module_sum(tensor_module(R, V, W).add, " +
				"    tensor_module(R, V, W).zero, " +
				"    T, " +
				"    λu:B. tensor(R, V, W, u, x(u))) = " +
				"tensor_module(R, V, W).zero",
			"d ∈ T",
		},
		Conclusion: "x(d) = W.zero",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[module_record.ModuleOps[A, B]],
			W *Expr[module_record.ModuleOps[A, C]],
			E, T *Expr[Set[B]],
			x *Arrow[B, C],
			d *Expr[B],
			moduleV, moduleW, finiteBasis, basis, inBasis, values, vanishing, dInT Fact,
		) {
			tensors := a.TermAs[module_record.ModuleOps[A, Set[Fun[Prod[B, C], A]]]]("tensor_module(R, V, W)")
			dInE := a.Have(
				"d is a basis element",
				"d ∈ E",
				BySets(dInT, inBasis))
			coordinate := a.Have(
				"the coordinate at d is a linear form",
				"module_homomorphism(R, V, regular_module(R), λv:B. module_basis_coordinates(R, V, E, v, d))",
				By(moduleV, finiteBasis, basis, dInE, module_dimension.BasisCoordinateLinear.At(R, V, E, d)))
			h, contraction := a.ObtainAs[Fun[Set[Fun[Prod[B, C], A]], C]](
				"contract the tensor product along that coordinate",
				"∃h:(set(prod(B, C) → A) → C). "+
					"    module_homomorphism(R, tensor_module(R, V, W), W, h) ∧ "+
					"    (∀u:B. ∀v:C. "+
					"        u ∈ V.carrier ∧ v ∈ W.carrier ⇒ "+
					"        h(tensor(R, V, W, u, v)) = W.smul(module_basis_coordinates(R, V, E, u, d), v))",
				By(
					coordinate,
					moduleW,
					TensorFunctional.At(R, V, W, a.TermAs[Fun[B, A]]("λv:B. module_basis_coordinates(R, V, E, v, d)"))))
			parts := a.Conjuncts(
				contraction,
				"h is linear",
				"h contracts a pure tensor")
			hLinear, hPure := parts[0], parts[1]
			finiteT := a.Have(
				"T is finite",
				"finite(T)",
				By(finiteBasis, inBasis, finite_set.FiniteSubset))
			members := a.Have(
				"a member of T is a basis element, and a vector",
				"∀u:B. u ∈ T ⇒ u ∈ E ∧ u ∈ V.carrier",
				BySets(inBasis, basis, linear_independence.BasisInCarrier.At(R, V, E)))
			tensorCarrier := a.Have(
				"the tensor module has the tensor product as its carrier",
				"tensor_module(R, V, W).carrier = tensor_product(R, V, W)",
				By(TensorModuleCarrier))
			pure := a.Have(
				"each u ⊗ x(u) lies in the tensor module",
				"∀u:B. u ∈ T ⇒ tensor(R, V, W, u, x(u)) ∈ tensor_module(R, V, W).carrier",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					inT := b.Assume()
					b.Show(
						"a pure tensor of two vectors",
						By(
							Normalized,
							members.At(u),
							inT,
							values.At(u),
							tensorCarrier,
							moduleV,
							moduleW,
							TensorIn.At(R, V, W, u, b.TermAs[C]("x(u)"))))
				}))
			summed := a.Have(
				"h carries the sum of tensors to the sum of their contractions",
				"h(module_sum(tensor_module(R, V, W).add, "+
					"        tensor_module(R, V, W).zero, "+
					"        T, "+
					"        λu:B. tensor(R, V, W, u, x(u)))) = "+
					"module_sum(W.add, W.zero, T, λu:B. h(tensor(R, V, W, u, x(u))))",
				By(
					finiteT,
					hLinear,
					pure,
					module_homomorphism.HomSum.At(
						R, tensors, W, h, T, a.TermAs[Fun[B, Set[Fun[Prod[B, C], A]]]]("λu:B. tensor(R, V, W, u, x(u))"))))
			contracted := a.Have(
				"the contraction of u ⊗ x(u) is x(u) at d and zero elsewhere",
				"∀u:B. u ∈ T ⇒ h(tensor(R, V, W, u, x(u))) = COND(u = d, x(u), W.zero)",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					inT := b.Assume()
					value := b.TermAs[C]("x(u)")
					delta := b.Have(
						"the coordinate at d of a basis element is a Kronecker delta",
						"module_basis_coordinates(R, V, E, u, d) = COND(d = u, R.one, R.zero)",
						By(
							Normalized,
							moduleV,
							finiteBasis,
							basis,
							members.At(u),
							inT,
							module_dimension.BasisCoordinateDelta.At(R, V, E, u)))
					b.Cases(b.Term("u = d"))
					b.When(
						"at d the coordinate is one",
						func(c *Argument, same Fact) {
							c.Show(
								"one fixes x(d)",
								By(
									hPure.At(u, value),
									delta,
									members.At(u),
									values.At(u),
									inT,
									moduleW,
									same,
									At(module.SmulOne.Read(moduleW), value)))
						})
					b.Otherwise(
						"off d the coordinate is zero",
						func(c *Argument, other Fact) {
							c.Show(
								"zero kills x(u)",
								By(
									hPure.At(u, value),
									delta,
									members.At(u),
									values.At(u),
									inT,
									moduleW,
									other,
									At(module.ZeroSmul.Read(moduleW), value)))
						})
				}))
			inTarget := a.Have(
				"each contraction lies in W",
				"∀u:B. u ∈ T ⇒ h(tensor(R, V, W, u, x(u))) ∈ W.carrier",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					inT := b.Assume()
					b.Show(
						"h maps into W",
						By(inT, pure.At(u), hLinear, module_homomorphism.HomIn.Read(hLinear)))
				}))
			offD := a.Have(
				"the contractions off d vanish",
				"∀u:B. u ∈ T ∧ u ≠ d ⇒ h(tensor(R, V, W, u, x(u))) = W.zero",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					guards := b.Assume()
					b.Show(
						"the conditional takes its second branch",
						By(guards, contracted.At(u)))
				}))
			single := a.Have(
				"only the term at d survives",
				"module_sum(W.add, W.zero, T, λu:B. h(tensor(R, V, W, u, x(u)))) = h(tensor(R, V, W, d, x(d)))",
				By(
					moduleW,
					finiteT,
					dInT,
					inTarget,
					offD,
					module.ModuleSumSingle.At(R, W, T, d, a.TermAs[Fun[B, C]]("λu:B. h(tensor(R, V, W, u, x(u)))"))))
			killed := a.Have(
				"h sends the vanishing sum to zero",
				"h(module_sum(tensor_module(R, V, W).add, "+
					"        tensor_module(R, V, W).zero, "+
					"        T, "+
					"        λu:B. tensor(R, V, W, u, x(u)))) = "+
					"W.zero",
				vanishing.Rw(),
				By(hLinear, module_homomorphism.HomZero.Read(hLinear)))
			a.Show(
				"so x(d) is zero",
				By(dInT, contracted.At(d), single, summed, killed))
		}),
})}

// TensorFunctional — a linear form p on V contracts the tensor product onto
// W: the map (u, v) ↦ p(u) • v is bilinear, so it factors through V ⊗ W.
var TensorFunctional = tensorFunctionalThm{family.Add(registry.ProofEntry{
	Name: "TensorFunctional",
	Key:  "prop_aae1a767f637d96b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀p:(B → A).",
		Hypotheses: []string{
			"module_homomorphism(R, V, regular_module(R), p)",
			"module_on(R, W)",
		},
		Conclusion: "∃h:(set(prod(B, C) → A) → C). " +
			"    module_homomorphism(R, tensor_module(R, V, W), W, h) ∧ " +
			"    (∀u:B. ∀v:C. u ∈ V.carrier ∧ v ∈ W.carrier ⇒ h(tensor(R, V, W, u, v)) = p(u) • v)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[module_record.ModuleOps[A, B]],
			W *Expr[module_record.ModuleOps[A, C]],
			p *Arrow[B, A],
			linear, target Fact,
		) {
			values := a.Have(
				"p takes its values in the scalars",
				"∀u:B. u ∈ V.carrier ⇒ p(u) ∈ R.carrier",
				By(module_homomorphism.HomIn.Read(linear)))
			inW := a.Have(
				"p(u) • v stays in W",
				"∀u:B. ∀v:C. u ∈ V.carrier ∧ v ∈ W.carrier ⇒ W.smul(p(u), v) ∈ W.carrier",
				By(module.SmulIn.Read(target), values))
			addLeft := a.Have(
				"additive in u, since p is",
				Statement{
					Binders: "∀u u₁:B. ∀v:C.",
					Hypotheses: []string{
						"u ∈ V.carrier",
						"u₁ ∈ V.carrier",
						"v ∈ W.carrier",
					},
					Conclusion: "W.smul(p(V.add(u, u₁)), v) = W.add(W.smul(p(u), v), W.smul(p(u₁), v))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					u1 := b.FixAs[B]("u₁")
					v := b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"p adds, then the scalars distribute over v",
						By(
							values,
							members,
							target,
							At(module_homomorphism.HomAdd.Read(linear), u, u1),
							At(module.SmulAddRight.Read(target), b.TermAs[A]("p(u)"), b.TermAs[A]("p(u₁)"), v)))
				}))
			addRight := a.Have(
				"additive in v",
				Statement{
					Binders: "∀u:B. ∀v v₁:C.",
					Hypotheses: []string{
						"u ∈ V.carrier",
						"v ∈ W.carrier",
						"v₁ ∈ W.carrier",
					},
					Conclusion: "W.smul(p(u), W.add(v, v₁)) = W.add(W.smul(p(u), v), W.smul(p(u), v₁))",
				},
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					v := b.FixAs[C]("v")
					v1 := b.FixAs[C]("v₁")
					members := b.Assume()
					b.Show(
						"p(u) distributes",
						By(values, members, target, At(module.SmulAddLeft.Read(target), b.TermAs[A]("p(u)"), v, v1)))
				}))
			scalarLeft := a.Have(
				"linear in u over the scalars",
				Statement{
					Binders: "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ V.carrier",
						"v ∈ W.carrier",
					},
					Conclusion: "W.smul(p(V.smul(c, u)), v) = W.smul(c, W.smul(p(u), v))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[B]("u")
					v := b.FixAs[C]("v")
					members := b.Assume()
					b.Show(
						"p takes the scalar out, then the action composes",
						By(
							values,
							members,
							target,
							At(module_homomorphism.HomSmul.Read(linear), c, u),
							At(module.SmulMul.Read(target), c, b.TermAs[A]("p(u)"), v)))
				}))
			scalarRight := a.Have(
				"linear in v over the scalars, the ring being commutative",
				Statement{
					Binders: "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ V.carrier",
						"v ∈ W.carrier",
					},
					Conclusion: "W.smul(p(u), W.smul(c, v)) = W.smul(c, W.smul(p(u), v))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[B]("u")
					v := b.FixAs[C]("v")
					members := b.Assume()
					value := b.TermAs[A]("p(u)")
					b.Show(
						"c and p(u) commute in the action",
						By(
							values.At(u),
							members,
							target,
							At(comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(module.RingOn.Read(target))), c, value),
							At(module.SmulMul.Read(target), c, value, v),
							At(module.SmulMul.Read(target), value, c, v)))
				}))
			bilinear := a.Have(
				"so (u, v) ↦ p(u) • v is bilinear",
				"bilinear_map(R, V, W, W, λu:B. λv:C. p(u) • v)",
				Simp(Fwd(module_homomorphism.BilinearMapDef), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				By(
					module_homomorphism.HomSource.Read(linear),
					scalarRight,
					scalarLeft,
					addLeft,
					addRight,
					inW,
					target))
			a.Show(
				"the universal property factors the bilinear map",
				By(
					bilinear,
					module_homomorphism.HomSource.Read(linear),
					TensorUniversal.At(R, V, W, W, a.TermAs[Fun2[B, C, C]]("λu:B. λv:C. p(u) • v"))))
		}),
})}

// TensorPureSum — every tensor is a finite sum of pure tensors: a scalar of
// the expansion the tensor product comes with is absorbed into the first
// factor.
var TensorPureSum = tensorPureSumThm{family.Add(registry.ProofEntry{
	Name: "TensorPureSum",
	Key:  "prop_2dafd02bbbf85ed3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀z:set(prod(B, C) → A).",
		Hypotheses: []string{
			"module_on(R, V)",
			"module_on(R, W)",
			"z ∈ tensor_product(R, V, W)",
		},
		Conclusion: "∃s:set(prod(B, C)). ∃b:(prod(B, C) → B). " +
			"    finite(s) ∧ " +
			"    s ⊆ set_cross(V.carrier, W.carrier) ∧ " +
			"    (∀q:prod(B, C). q ∈ s ⇒ b(q) ∈ V.carrier) ∧ " +
			"    z = " +
			"    module_sum(tensor_module(R, V, W).add, " +
			"        tensor_module(R, V, W).zero, " +
			"        s, " +
			"        λq:prod(B, C). tensor(R, V, W, b(q), snd(q)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[module_record.ModuleOps[A, B]],
			W *Expr[module_record.ModuleOps[A, C]],
			z *Expr[Set[Fun[Prod[B, C], A]]],
			moduleV, moduleW, inTensor Fact,
		) {
			operations := a.Conjuncts(
				a.Have(
					"the tensor module adds cosets, and its zero is the coset of the relations",
					"tensor_module(R, V, W).add = set_mul(fun_add(R.add)) ∧ "+
						"tensor_module(R, V, W).zero = tensor_relations(R, V, W)",
					Simp(Fwd(TensorModuleDef), Fwd(submodule.QuotientModuleDef)),
					Basic()),
				"the addition",
				"the zero")
			a.Do(operations[0].Rw(), operations[1].Rw())
			s, _, spanned := a.Obtain2As[Set[Prod[B, C]], Fun[Prod[B, C], A]](
				"z is a finite sum of scaled pure tensors",
				"∃s:set(prod(B, C)). ∃c:(prod(B, C) → A). "+
					"    finite(s) ∧ "+
					"    s ⊆ set_cross(V.carrier, W.carrier) ∧ "+
					"    (∀q:prod(B, C). q ∈ s ⇒ c(q) ∈ R.carrier) ∧ "+
					"    z = "+
					"    module_sum(set_mul(fun_add(R.add)), "+
					"        tensor_relations(R, V, W), "+
					"        s, "+
					"        λq:prod(B, C). "+
					"            quotient_smul(fun_add(R.add), "+
					"                fun_smul(R.mul), "+
					"                tensor_relations(R, V, W), "+
					"                c(q), "+
					"                tensor(R, V, W, fst(q), snd(q))))",
				By(moduleV, moduleW, inTensor, TensorSpan.At(R, V, W, z)))
			parts := a.Conjuncts(
				spanned,
				"the index set is finite",
				"the indices are pairs of vectors",
				"the coefficients are scalars",
				"z is their sum")
			finiteIndices, pairs, coefficients, expansion := parts[0], parts[1], parts[2], parts[3]
			absorbed := a.Have(
				"each scalar moves into the first factor",
				Statement{
					Binders: "∀q:prod(B, C).",
					Hypotheses: []string{
						"q ∈ s",
					},
					Conclusion: "V.smul(c(q), fst(q)) ∈ V.carrier ∧ " +
						"quotient_smul(fun_add(R.add), " +
						"    fun_smul(R.mul), " +
						"    tensor_relations(R, V, W), " +
						"    c(q), " +
						"    tensor(R, V, W, fst(q), snd(q))) = " +
						"tensor(R, V, W, V.smul(c(q), fst(q)), snd(q))",
				},
				Derive(func(b *Argument) {
					q := b.FixAs[Prod[B, C]]("q")
					inIndices := b.Assume()
					scalar := b.TermAs[A]("c(q)")
					first := b.TermAs[B]("fst(q)")
					second := b.TermAs[C]("snd(q)")
					factors := b.Have(
						"the two components of q lie in V and W",
						"fst(q) ∈ V.carrier ∧ snd(q) ∈ W.carrier",
						BySets(
							inIndices,
							pairs,
							set_product.InCrossProjections.At(b.TermAs[Set[B]]("V.carrier"), b.TermAs[Set[C]]("W.carrier"), q)))
					b.Show(
						"a scalar moves across the tensor sign",
						By(
							inIndices,
							coefficients.At(q),
							factors,
							moduleV,
							moduleW,
							At(module.SmulIn.Read(moduleV), scalar, first),
							TensorSmulLeft.At(R, V, W, scalar, first, second)))
				}))
			a.Take(s)
			a.Take(a.TermAs[Fun[Prod[B, C], B]]("λq:prod(B, C). V.smul(c(q), fst(q))"))
			a.Show(
				"the absorbed scalars give the same sum, term by term",
				By(
					finiteIndices,
					pairs,
					absorbed,
					expansion,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[Set[Fun[Prod[B, C], A]]]]("set_mul(fun_add(R.add))"),
						a.TermAs[Set[Fun[Prod[B, C], A]]]("tensor_relations(R, V, W)"),
						s,
						a.TermAs[Fun[Prod[B, C], Set[Fun[Prod[B, C], A]]]](
							"λq:prod(B, C). "+
								"    quotient_smul(fun_add(R.add), "+
								"        fun_smul(R.mul), "+
								"        tensor_relations(R, V, W), "+
								"        c(q), "+
								"        tensor(R, V, W, fst(q), snd(q)))"),
						a.TermAs[Fun[Prod[B, C], Set[Fun[Prod[B, C], A]]]](
							"λq:prod(B, C). tensor(R, V, W, V.smul(c(q), fst(q)), snd(q))"))))
		}),
})}
