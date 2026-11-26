// linear_independence.go — the chapter: independent sets and bases of a
// module on a set, the span as the set of finite combinations, and over
// a field the exchange lemma, the existence of bases and the replacement
// theorem.

package linear_independence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// ModuleIndependentDef — `module_independent(R, M, S)`: S is a subset of
// M's carrier on which only the zero combination vanishes. A
// combination is a finite sum over a finite part T of S, each member
// scaled by its own coefficient a(x) from R's carrier; the set indexes
// its own combinations, so no index type and no family of vectors
// stands between a set and its independence.
var ModuleIndependentDef = moduleIndependentDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleIndependentDef",
	Key:   "prop_ced0b2d9c1d0c46c",
	Const: "module_independent",
	Type:  "ring_ops(A) → module_ops(A, B) → set(B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(B). " +
			"    module_independent(R, M, S) ⇔ " +
			"    S ⊆ M.carrier ∧ " +
			"    (∀T:set(B). ∀a:(B → A). " +
			"        finite(T) ∧ " +
			"        T ⊆ S ∧ " +
			"        (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ " +
			"        module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero ⇒ " +
			"        (∀x:B. x ∈ T ⇒ a(x) = R.zero))",
	},
})}

// ModuleBasisDef — `module_basis(R, M, S)`: an independent subset of M's
// carrier whose span is the carrier.
var ModuleBasisDef = moduleBasisDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleBasisDef",
	Key:   "prop_26f5b0b81c5b850a",
	Const: "module_basis",
	Type:  "ring_ops(A) → module_ops(A, B) → set(B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(B). " +
			"    module_basis(R, M, S) ⇔ module_independent(R, M, S) ∧ module_span(R, M, S) = M.carrier",
	},
	Deps: []registry.EntryLike{ModuleIndependentDef},
})}

// IndependentInCarrier — an independent set lies in M's carrier.
var IndependentInCarrier = independentInCarrierThm{family.Add(registry.ProofEntry{
	Name:  "IndependentInCarrier",
	Key:   "prop_50847066be0a4517",
	Build: ModuleIndependentDef.Entry().Conjunct("S ⊆ M.carrier"),
})}

// BasisInCarrier — a basis lies in M's carrier: it is independent, and an
// independent set lies in the carrier.
var BasisInCarrier = basisInCarrierThm{family.Add(registry.ProofEntry{
	Name: "BasisInCarrier",
	Key:  "prop_8656dd8401d0994c",
	Build: ModuleBasisDef.Entry().Law("S ⊆ M.carrier",
		func(a *Argument, basis Fact) {
			onS := a.Conjuncts(
				a.Unfolded(basis, ModuleBasisDef),
				"S is independent",
				"S spans M")
			a.Show(
				"S, being independent, lies in M",
				By(IndependentInCarrier.Read(onS[0])))
		}),
})}

// IndependentVanishingCombination — a vanishing combination over a
// finite part of an independent set has every coefficient zero.
var IndependentVanishingCombination = independentVanishingCombinationThm{family.Add(registry.ProofEntry{
	Name: "IndependentVanishingCombination",
	Key:  "prop_fd931600a806ee7f",
	Build: ModuleIndependentDef.Entry().Conjunct(Statement{
		Binders: "∀T:set(B). ∀a:(B → A). ∀z:B.",
		Hypotheses: []string{
			"finite(T)",
			"T ⊆ S",
			"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
			"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero",
			"z ∈ T",
		},
		Conclusion: "a(z) = R.zero",
	}),
})}

// ---------------------------------------------------------------------------
// Finite combinations
// ---------------------------------------------------------------------------

// CombinationExtendByZero — off T the extended coefficient is R.zero,
// which scales every vector of M to M.zero, so the sum over U is the sum
// over T; on T the extended coefficient is a's.
var CombinationExtendByZero = combinationExtendByZeroThm{family.Add(registry.ProofEntry{
	Name: "CombinationExtendByZero",
	Key:  "prop_df18be83f514ae2c",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀T U:set(B). ∀a:(B → A).",
		Hypotheses: []string{
			"finite(U)",
			"T ⊆ U",
			"U ⊆ M.carrier",
			"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, U, λx:B. COND(x ∈ T, a(x), R.zero) • x) = " +
			"module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			T, U *Expr[Set[B]],
			a *Arrow[B, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"U is finite",
				"T lies in U",
				"U lies in M",
				"a is a scalar on T")
			finU, tInU, uInM, scalars := parts[0], parts[1], parts[2], parts[3]
			inM := arg.Unfolded(uInM, set_basic.SubsetDef)
			vecAdd, vecZero := arg.TermAs[Op[B]]("M.add"), arg.TermAs[B]("M.zero")
			extended := arg.TermAs[Fun[B, B]]("λx:B. COND(x ∈ T, a(x), R.zero) • x")
			coefficients := arg.Have(
				"the extended coefficient is a scalar: a(x) on T, R.zero off it",
				"∀x:B. COND(x ∈ T, a(x), R.zero) ∈ R.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(scalars.At(x), comm_ring.ZeroIn.Read(module.RingOn.Read(moduleOn)))
				}))
			terms := arg.Have(
				"so each extended term over U lies in M",
				"∀x:B. x ∈ U ⇒ COND(x ∈ T, a(x), R.zero) • x ∈ M.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), coefficients.At(x), module.SmulIn.Read(moduleOn))
				}))
			vanish := arg.Have(
				"off T the extended term is R.zero • x, which is M.zero",
				"∀x:B. x ∈ U ∧ x ∉ T ⇒ COND(x ∈ T, a(x), R.zero) • x = M.zero",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), module.ZeroSmul.Read(moduleOn).AsFact().At(x))
				}))
			agree := arg.Have(
				"on T it is a(x) • x",
				"∀x:B. x ∈ T ⇒ COND(x ∈ T, a(x), R.zero) • x = a(x) • x",
				Derive(func(b *Argument) {
					b.FixAs[B]("x")
					b.Show(
						"x ∈ T selects the coefficient a(x)",
						By(b.Assume()))
				}))
			arg.Show(
				"the extended terms vanish on U off T and are a's on T",
				CalcEq(
					Leg(
						arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. COND(x ∈ T, a(x), R.zero) • x)"),
						"the terms off T vanish",
						By(finU, tInU, terms, vanish, module.ModuleSumSupport.Read(moduleOn).At(U, T, extended))),
					FinalLeg(
						"and those on T are a's",
						By(
							agree,
							module.ModuleSumCongruence.At(
								vecAdd, vecZero, T, extended, arg.TermAs[Fun[B, B]]("λx:B. a(x) • x")))),
				))
		}),
})}

// CombinationAdd — M adds the two finite sums termwise, and at each index
// the two scalings of x add to the scaling by the sum of the coefficients.
var CombinationAdd = combinationAddThm{family.Add(registry.ProofEntry{
	Name: "CombinationAdd",
	Key:  "prop_bc40a42703aaebe1",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀T:set(B). ∀a b:(B → A).",
		Hypotheses: []string{
			"finite(T)",
			"T ⊆ M.carrier",
			"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier ∧ b(x) ∈ R.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, T, λx:B. a(x) • x) + " +
			"module_sum(M.add, M.zero, T, λx:B. b(x) • x) = " +
			"module_sum(M.add, M.zero, T, λx:B. (a(x) + b(x)) • x)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			T *Expr[Set[B]],
			a, b *Arrow[B, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"T is finite",
				"T lies in M",
				"a and b are scalars on T")
			finT, tInM, scalars := parts[0], parts[1], parts[2]
			inM := arg.Unfolded(tInM, set_basic.SubsetDef)
			vecAdd, vecZero := arg.TermAs[Op[B]]("M.add"), arg.TermAs[B]("M.zero")
			termwise := arg.TermAs[Fun[B, B]]("λx:B. a(x) • x + b(x) • x")
			terms := arg.Have(
				"both terms at an index of T lie in M",
				"∀x:B. x ∈ T ⇒ a(x) • x ∈ M.carrier ∧ b(x) • x ∈ M.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), scalars.At(x), module.SmulIn.Read(moduleOn))
				}))
			distribute := arg.Have(
				"a(x) • x + b(x) • x is (a(x) + b(x)) • x",
				"∀x:B. x ∈ T ⇒ a(x) • x + b(x) • x = (a(x) + b(x)) • x",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), scalars.At(x), module.SmulAddRight.Read(moduleOn))
				}))
			arg.Show(
				"the sum of two finite sums is the finite sum of the termwise sums",
				CalcEq(
					Leg(
						arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. a(x) • x + b(x) • x)"),
						"M adds two finite sums over T termwise",
						By(
							finT,
							terms,
							module.ModuleSumAdd.Read(moduleOn).At(
								T, arg.TermAs[Fun[B, B]]("λx:B. a(x) • x"), arg.TermAs[Fun[B, B]]("λx:B. b(x) • x")))),
					FinalLeg(
						"and the coefficients add",
						By(
							distribute,
							module.ModuleSumCongruence.At(vecAdd, vecZero, T,
								termwise, arg.TermAs[Fun[B, B]]("λx:B. (a(x) + b(x)) • x")))),
				))
		}),
})}

// CombinationScale — c distributes over the finite sum of members of M,
// and scaling x by a(x) and then by c is scaling it by c * a(x).
var CombinationScale = combinationScaleThm{family.Add(registry.ProofEntry{
	Name: "CombinationScale",
	Key:  "prop_bf6ec6f896f30c0e",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀T:set(B). ∀c:A. ∀a:(B → A).",
		Hypotheses: []string{
			"finite(T)",
			"T ⊆ M.carrier",
			"c ∈ R.carrier",
			"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
		},
		Conclusion: "c • module_sum(M.add, M.zero, T, λx:B. a(x) • x) = " +
			"module_sum(M.add, M.zero, T, λx:B. c * a(x) • x)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			T *Expr[Set[B]],
			c *Expr[A],
			a *Arrow[B, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"T is finite",
				"T lies in M",
				"c is a scalar",
				"a is a scalar on T")
			finT, tInM, cIn, scalars := parts[0], parts[1], parts[2], parts[3]
			inM := arg.Unfolded(tInM, set_basic.SubsetDef)
			cR := arg.MemberOf[on.R](c, cIn)
			vecAdd, vecZero := arg.TermAs[Op[B]]("M.add"), arg.TermAs[B]("M.zero")
			terms := arg.Have(
				"each term a(x) • x lies in M",
				"∀x:B. x ∈ T ⇒ a(x) • x ∈ M.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), scalars.At(x), module.SmulIn.Read(moduleOn))
				}))
			regroup := arg.Have(
				"c • (a(x) • x) is (c * a(x)) • x",
				"∀x:B. x ∈ T ⇒ c • (a(x) • x) = (c * a(x)) • x",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), scalars.At(x), cIn, module.SmulMul.Read(moduleOn))
				}))
			arg.Show(
				"c scales the sum term by term, each term by the product",
				CalcEq(
					Leg(
						arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. c • (a(x) • x))"),
						"c distributes over a finite sum of members of M",
						By(
							finT,
							cIn,
							terms,
							module.ModuleSumSmul.Read(moduleOn).At(T, cR, arg.TermAs[Fun[B, B]]("λx:B. a(x) • x")))),
					FinalLeg(
						"and scaling twice is scaling by the product",
						By(
							regroup,
							module.ModuleSumCongruence.At(vecAdd, vecZero, T,
								arg.TermAs[Fun[B, B]]("λx:B. c • (a(x) • x)"), arg.TermAs[Fun[B, B]]("λx:B. (c * a(x)) • x")))),
				))
		}),
})}

// CombinationPair — a combination of two distinct members u and v of M
// is its two terms: {u, v} is u laid into {v}, which u is not in
// (ModuleSumInsert), and the sum over {v} is its one term
// (ModuleSumSingle).
var CombinationPair = combinationPairThm{family.Add(registry.ProofEntry{
	Name: "CombinationPair",
	Key:  "prop_480e29a82548afc2",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀u v:B. ∀a:(B → A).",
		Hypotheses: []string{
			"u ∈ M.carrier",
			"v ∈ M.carrier",
			"u ≠ v",
			"a(u) ∈ R.carrier",
			"a(v) ∈ R.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, {u, v}, λx:B. a(x) • x) = a(u) • u + a(v) • v",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			u, v *Expr[B],
			a *Arrow[B, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"u lies in M",
				"so does v",
				"u is not v",
				"a(u) is a scalar",
				"so is a(v)")
			uIn, vIn, apart, au, av := parts[0], parts[1], parts[2], parts[3], parts[4]
			single := arg.TermAs[Set[B]]("{v}")
			term := arg.TermAs[Fun[B, B]]("λx:B. a(x) • x")
			termU := arg.Have(
				"a(u) • u lies in M",
				"a(u) • u ∈ M.carrier",
				By(uIn, au, module.SmulIn.Read(moduleOn)))
			termV := arg.Have(
				"and so does a(v) • v",
				"a(v) • v ∈ M.carrier",
				By(vIn, av, module.SmulIn.Read(moduleOn)))
			onSingle := arg.Have(
				"the one term over {v} lies in M",
				"∀x:B. x ∈ {v} ⇒ a(x) • x ∈ M.carrier",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					isV := b.Have(
						"x is v",
						"x = v",
						By(b.Assume(), set_basic.InSing.At(x, v)))
					b.Show(
						"so its term is the term at v",
						isV.Rw(),
						By(termV))
				}))
			offV := arg.Have(
				"and {v} has no member but v",
				"∀x:B. x ∈ {v} ∧ x ≠ v ⇒ a(x) • x = M.zero",
				BySets())
			finiteSingle := finite_set.FiniteSing.At(v)
			arg.Show(
				"the sum over {u, v} is the term at u plus the sum over {v}, its term at v",
				CalcEq(
					Leg(
						arg.TermAs[B]("a(u) • u + module_sum(M.add, M.zero, {v}, λx:B. a(x) • x)"),
						"u is laid into {v}, which it is not in",
						By(
							finiteSingle,
							apart,
							set_basic.InSing.At(u, v),
							termU,
							onSingle,
							module.ModuleSumInsert.Read(moduleOn).At(single, u, term))),
					FinalLeg(
						"and the sum over {v} is its one term",
						By(
							finiteSingle,
							set_basic.InSing.At(v, v),
							onSingle,
							offV,
							module.ModuleSumSingle.Read(moduleOn).At(single, v, term))),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The span as combinations, over any ring
// ---------------------------------------------------------------------------

// combinations is the set of the finite combinations of S: the sums over a
// finite part T of S, each member x scaled by its coefficient a(x) from R.
const combinations = "{module_sum(M.add, M.zero, T, λx:B. a(x) • x) | " +
	"T:set(B), a:(B → A) | finite(T) ∧ T ⊆ S ∧ (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier)}"

// SpanCombinations — the span of a subset of M is the set of its finite
// combinations: those form a submodule holding the set, and every
// submodule holding the set holds them.
var SpanCombinations = spanCombinationsThm{family.Add(registry.ProofEntry{
	Name: "SpanCombinations",
	Key:  "prop_2f460dc32bbb7d38",
	Reading: "S ⊆ M.carrier is load-bearing: for S ⊄ M no submodule of M " +
		"holds S, the span is ⋂∅ = 𝕌, while the combinations need not be all of B.",
	Build: module.ModuleOn.Law("∀S:set(B). S ⊆ M.carrier ⇒ module_span(R, M, S) = "+combinations,
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], S *Expr[Set[B]], sInM Fact) {
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			ring := module.RingOn.Read(moduleOn)
			additive := module.AddGroupOn.Read(moduleOn)
			vecAdd, vecZero := arg.TermAs[Op[B]]("M.add"), arg.TermAs[B]("M.zero")
			carrier := arg.TermAs[Set[B]]("M.carrier")
			empty := arg.TermAs[Set[B]]("∅")
			finEmpty := arg.Have(
				"∅ is finite",
				"finite(∅⟨A:B⟩)",
				By(finite_set.FiniteRules))
			zeroIn := comm_ring.ZeroIn.Read(ring)
			oneIn := arg.Have(
				"R.one is a scalar",
				"R.one ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring)))
			one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), oneIn)

			// C, the finite combinations of S, read as a membership.
			C, combinationsDef := arg.LetAs[Set[B]]("C", combinations)
			span := arg.TermAs[Set[B]]("module_span(R, M, S)")
			inC := arg.Have(
				"w lies in C exactly when it is a combination of S",
				"∀w:B. "+
					"    w ∈ C ⇔ "+
					"    ∃T:set(B). ∃a:(B → A). "+
					"        finite(T) ∧ "+
					"        T ⊆ S ∧ "+
					"        (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ "+
					"        w = module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
				BySets(combinationsDef))
			combination := arg.Have(
				"so every combination of S lies in C",
				Statement{
					Binders: "∀T:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ S",
						"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
					},
					Conclusion: "module_sum(M.add, M.zero, T, λx:B. a(x) • x) ∈ C",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[B]]("T")
					a := b.FixAs[Fun[B, A]]("a")
					given := b.Assume()
					witnessed := b.Have(
						"T and a witness it",
						"∃T':set(B). ∃a':(B → A). "+
							"    finite(T') ∧ "+
							"    T' ⊆ S ∧ "+
							"    (∀x:B. x ∈ T' ⇒ a'(x) ∈ R.carrier) ∧ "+
							"    module_sum(M.add, M.zero, T, λx:B. a(x) • x) = module_sum(M.add, M.zero, T', λx:B. a'(x) • x)",
						Derive(func(c *Argument) {
							c.Take(T)
							c.Take(a)
							c.Show(
								"the combination of a over T is itself",
								By(given))
						}))
					b.Show(
						"so it lies in C",
						By(witnessed, inC.At(b.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. a(x) • x)"))))
				}))

			// ⊇: a submodule N holding S holds C.
			within := arg.Have(
				"C lies in every submodule that holds S",
				"∀N:set(B). submodule(R, M, N) ∧ S ⊆ N ⇒ C ⊆ N",
				Derive(func(b *Argument) {
					N := b.FixAs[Set[B]]("N")
					assumed := b.Conjuncts(
						b.Assume(),
						"N is a submodule",
						"N holds S")
					isSubmodule, sInN := assumed[0], assumed[1]
					inN := b.Unfolded(sInN, set_basic.SubsetDef)
					pointwise := b.Have(
						"a member w of C is a sum of members of N",
						"∀w:B. w ∈ C ⇒ w ∈ N",
						Derive(func(c *Argument) {
							w := c.FixAs[B]("w")
							T, _, wIs := c.Obtain2As[Set[B], Fun[B, A]](
								"w is a combination over some finite T ⊆ S",
								"∃T:set(B). ∃a:(B → A). "+
									"    finite(T) ∧ "+
									"    T ⊆ S ∧ "+
									"    (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ "+
									"    w = module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
								By(inC.At(w), c.Assume()))
							about := c.Conjuncts(
								wIs,
								"T is finite",
								"T lies in S",
								"a is a scalar on T",
								"w is the combination of a over T")
							finT, tInS, scalars, wIsSum := about[0], about[1], about[2], about[3]
							inS := c.Unfolded(tInS, set_basic.SubsetDef)
							terms := c.Have(
								"N is closed under scaling, so each term a(x) • x lies in N",
								"∀x:B. x ∈ T ⇒ a(x) • x ∈ N",
								Derive(func(d *Argument) {
									x := d.FixAs[B]("x")
									d.Show(
										"a(x) is a scalar and x lies in N",
										By(
											inS.At(x),
											inN.At(x),
											scalars.At(x),
											submodule.SubmoduleSmul.Read(isSubmodule).AsFact().At(d.TermAs[A]("a(x)"), x)))
								}))
							c.Show(
								"a submodule holds every finite sum of its vectors",
								By(
									Normalized,
									wIsSum,
									isSubmodule,
									finT,
									terms,
									submodule.SubmoduleModuleSum.Read(moduleOn).At(N, T, c.TermAs[Fun[B, B]]("λx:B. a(x) • x"))))
						}))
					b.Show(
						"so C lies in N",
						BySets(pointwise))
				}))
			cInM := arg.Have(
				"C lies in M, whose carrier is a submodule holding S",
				"C ⊆ M.carrier",
				By(within.At(carrier), moduleOn, sInM, submodule.CarrierSubmodule.At(R, M)))
			cInSpan := arg.Have(
				"and C lies in the span, a submodule holding S",
				"C ⊆ module_span(R, M, S)",
				By(
					within.At(span),
					moduleOn,
					sInM,
					submodule.SpanSubmodule.At(R, M, S),
					submodule.SubsetSpan.At(R, M, S)))

			// ⊆: C is a submodule holding S.
			zeroInC := arg.Have(
				"M.zero lies in C: it is the combination over ∅",
				"M.zero ∈ C",
				By(
					module.ModuleSumEmpty.At(vecAdd, vecZero, arg.TermAs[Fun[B, B]]("λx:B. R.zero • x")),
					combination.At(empty, arg.TermAs[Fun[B, A]]("λx:B. R.zero")),
					finEmpty,
					set_order.EmptySubset.At(S),
					zeroIn))
			singles := arg.Have(
				"each v of S is the combination over {v} with the coefficient R.one",
				"∀v:B. v ∈ S ⇒ v ∈ C",
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					vInS := b.Assume()
					inM := b.Unfolded(sInM, set_basic.SubsetDef)
					vM := b.MemberOf[on.M](v, b.Have(
						"v lies in M",
						"v ∈ M.carrier",
						By(inM.At(v), vInS)))
					ones := b.TermAs[Fun[B, B]]("λx:B. R.one • x")
					single := b.Have(
						"the combination over {v} with the coefficient R.one is v",
						"module_sum(M.add, M.zero, {v}, λx:B. R.one • x) = v",
						CalcEq(
							Leg(
								b.TermAs[B]("R.one • v + module_sum(M.add, M.zero, ∅, λx:B. R.one • x)"),
								"{v} is v laid into ∅",
								By(
									finEmpty,
									set_basic.NotInEmpty.At(v),
									set_basic.NotInEmpty,
									module.SmulIn.Read(moduleOn).At(one, vM),
									module.ModuleSumInsert.Read(moduleOn).At(empty, v, ones))),
							Leg(
								b.TermAs[B]("v + M.zero"),
								"R.one fixes v, and the empty sum is M.zero",
								By(module.SmulOne.Read(moduleOn).At(vM), module.ModuleSumEmpty.At(vecAdd, vecZero, ones))),
							FinalLeg(
								"M.zero is the unit of +",
								By(group.RightIdentityOn.Read(additive).At(vM))),
						))
					b.Show(
						"so v is a combination of S",
						By(
							Normalized,
							single,
							combination.At(b.TermAs[Set[B]]("{v}"), b.TermAs[Fun[B, A]]("λx:B. R.one")),
							finite_set.FiniteSing.At(v),
							set_order.SingSubset.At(S, v),
							vInS,
							oneIn))
				}))
			sInC := arg.Have(
				"S lies in C",
				"S ⊆ C",
				BySets(singles))

			sums := arg.Have(
				"C is closed under +: u and v extend by zero to the "+
					"union of their index sets, where they add coefficientwise",
				"∀u v:B. u ∈ C ∧ v ∈ C ⇒ u + v ∈ C",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					v := b.FixAs[B]("v")
					assumed := b.Conjuncts(
						b.Assume(),
						"u lies in C",
						"v lies in C")
					T1, a1, uIs := b.Obtain2As[Set[B], Fun[B, A]](
						"u is a combination over some finite T₁ ⊆ S",
						"∃T₁:set(B). ∃a₁:(B → A). "+
							"    finite(T₁) ∧ "+
							"    T₁ ⊆ S ∧ "+
							"    (∀x:B. x ∈ T₁ ⇒ a₁(x) ∈ R.carrier) ∧ "+
							"    u = module_sum(M.add, M.zero, T₁, λx:B. a₁(x) • x)",
						By(inC.At(u), assumed[0]))
					T2, a2, vIs := b.Obtain2As[Set[B], Fun[B, A]](
						"v is a combination over some finite T₂ ⊆ S",
						"∃T₂:set(B). ∃a₂:(B → A). "+
							"    finite(T₂) ∧ "+
							"    T₂ ⊆ S ∧ "+
							"    (∀x:B. x ∈ T₂ ⇒ a₂(x) ∈ R.carrier) ∧ "+
							"    v = module_sum(M.add, M.zero, T₂, λx:B. a₂(x) • x)",
						By(inC.At(v), assumed[1]))
					first := b.Conjuncts(
						uIs,
						"T₁ is finite",
						"T₁ lies in S",
						"a₁ is a scalar on T₁",
						"u is the combination of a₁ over T₁")
					second := b.Conjuncts(
						vIs,
						"T₂ is finite",
						"T₂ lies in S",
						"a₂ is a scalar on T₂",
						"v is the combination of a₂ over T₂")
					union := b.TermAs[Set[B]]("T₁ ∪ T₂")
					finUnion := b.Have(
						"T₁ ∪ T₂ is finite",
						"finite(T₁ ∪ T₂)",
						By(first[0], second[0], finite_set.FiniteUnion.At(T1, T2)))
					unionInS := b.Have(
						"and lies in S",
						"T₁ ∪ T₂ ⊆ S",
						By(first[1], second[1], set_order.UnionSubset.At(T1, T2, S)))
					unionInM := b.Have(
						"and so in M",
						"T₁ ∪ T₂ ⊆ M.carrier",
						By(unionInS, sInM, set_order.SubsetTrans.At(union, S, carrier)))
					scalars := b.Have(
						"the coefficients extended by zero are scalars",
						"∀x:B. COND(x ∈ T₁, a₁(x), R.zero) ∈ R.carrier ∧ COND(x ∈ T₂, a₂(x), R.zero) ∈ R.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(first[2].At(x), second[2].At(x), zeroIn)
						}))
					uExtended := b.Have(
						"u is the combination over T₁ ∪ T₂ of a₁ extended by zero",
						"u = module_sum(M.add, M.zero, T₁ ∪ T₂, λx:B. COND(x ∈ T₁, a₁(x), R.zero) • x)",
						By(
							first[3],
							finUnion,
							unionInM,
							first[2],
							set_order.SubsetUnion.At(T1, T2),
							CombinationExtendByZero.Read(moduleOn).At(T1, union, a1)))
					vExtended := b.Have(
						"v is the combination over T₁ ∪ T₂ of a₂ extended by zero",
						"v = module_sum(M.add, M.zero, T₁ ∪ T₂, λx:B. COND(x ∈ T₂, a₂(x), R.zero) • x)",
						By(
							second[3],
							finUnion,
							unionInM,
							second[2],
							set_order.SubsetUnion.At(T2, T1),
							CombinationExtendByZero.Read(moduleOn).At(T2, union, a2)))
					sum := b.Have(
						"so u + v is the combination over T₁ ∪ T₂ of the extended coefficients added",
						"u + v = "+
							"module_sum(M.add, "+
							"    M.zero, "+
							"    T₁ ∪ T₂, "+
							"    λx:B. (COND(x ∈ T₁, a₁(x), R.zero) + COND(x ∈ T₂, a₂(x), R.zero)) • x)",
						By(
							uExtended,
							vExtended,
							finUnion,
							unionInM,
							scalars,
							CombinationAdd.Read(moduleOn).At(
								union,
								b.TermAs[Fun[B, A]]("λx:B. COND(x ∈ T₁, a₁(x), R.zero)"),
								b.TermAs[Fun[B, A]]("λx:B. COND(x ∈ T₂, a₂(x), R.zero)"))))
					coefficients := b.Have(
						"whose coefficients are scalars",
						"∀x:B. COND(x ∈ T₁, a₁(x), R.zero) + COND(x ∈ T₂, a₂(x), R.zero) ∈ R.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(scalars.At(x), comm_ring.AddIn.Read(ring))
						}))
					b.Show(
						"so u + v is a combination of S",
						By(
							sum,
							finUnion,
							unionInS,
							coefficients,
							combination.At(
								union, b.TermAs[Fun[B, A]]("λx:B. COND(x ∈ T₁, a₁(x), R.zero) + COND(x ∈ T₂, a₂(x), R.zero)"))))
				}))

			scalings := arg.Have(
				"C is closed under scaling: c • u is the combination of the coefficients c * a(x)",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ C ⇒ c • u ∈ C",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[B]("u")
					assumed := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in C")
					cIn, uInC := assumed[0], assumed[1]
					cR := b.MemberOf[on.R](c, cIn)
					T, a, uIs := b.Obtain2As[Set[B], Fun[B, A]](
						"u is a combination over some finite T ⊆ S",
						"∃T:set(B). ∃a:(B → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ S ∧ "+
							"    (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ "+
							"    u = module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
						By(inC.At(u), uInC))
					about := b.Conjuncts(
						uIs,
						"T is finite",
						"T lies in S",
						"a is a scalar on T",
						"u is the combination of a over T")
					finT, tInS, scalars, uIsSum := about[0], about[1], about[2], about[3]
					tInM := b.Have(
						"so T lies in M, as S does",
						"T ⊆ M.carrier",
						By(tInS, sInM, set_order.SubsetTrans.At(T, S, carrier)))
					products := b.Have(
						"and c * a(x) is a scalar",
						"∀x:B. x ∈ T ⇒ c * a(x) ∈ R.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(scalars.At(x), cIn, comm_ring.MulIn.Read(ring))
						}))
					scaled := b.Have(
						"c • u is the combination over T of the coefficients c * a(x)",
						"c • u = module_sum(M.add, M.zero, T, λx:B. (c * a(x)) • x)",
						By(uIsSum, finT, tInM, scalars, CombinationScale.Read(moduleOn).At(T, cR, a)))
					b.Show(
						"so c • u is a combination of S",
						By(scaled, finT, tInS, products, combination.At(T, b.TermAs[Fun[B, A]]("λx:B. c * a(x)"))))
				}))

			isSubmodule := arg.Have(
				"C is a submodule of M: it lies in M, holds M.zero, and is closed under + and scaling",
				"submodule(R, M, C)",
				By(cInM, zeroInC, sums, scalings, submodule.SubmoduleCriterion.Read(moduleOn).At(C)))
			spanInC := arg.Have(
				"so the span, the least submodule holding S, lies in C",
				"module_span(R, M, S) ⊆ C",
				By(isSubmodule, sInC, submodule.SpanLeast.At(R, M, S, C)))
			arg.Show(
				"C lies in the span as well, so the two are one set",
				By(spanInC, cInSpan, set_order.SubsetAntisym.At(span, C)))
		}),
})}

// SpanMembership — SpanCombinations read at one vector: the span is the
// set of combinations, and a member of that set is one of them.
var SpanMembership = spanMembershipThm{family.Add(registry.ProofEntry{
	Name: "SpanMembership",
	Key:  "prop_18b303f17c7469b7",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B). ∀v:B.",
		Hypotheses: []string{
			"S ⊆ M.carrier",
		},
		Conclusion: "v ∈ module_span(R, M, S) ⇔ " +
			"∃T:set(B). ∃a:(B → A). " +
			"    finite(T) ∧ " +
			"    T ⊆ S ∧ " +
			"    (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ " +
			"    v = module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			S *Expr[Set[B]],
			v *Expr[B],
			sInM Fact,
		) {
			arg.Show(
				"S lies in M, so its span is the set of its combinations, "+
					"which v lies in exactly when it is one of them",
				BySets(sInM, SpanCombinations.Read(moduleOn).At(S)))
		}),
})}

// SpanRestrict — the span of a subset of a submodule N is the same in M
// restricted to N as in M: the restriction is a module, so in both the
// span is the set of the finite combinations of S, and the restriction's
// sums and scalings are M's.
var SpanRestrict = spanRestrictThm{family.Add(registry.ProofEntry{
	Name: "SpanRestrict",
	Key:  "prop_a733e1986c93b318",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N S:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"S ⊆ N",
		},
		Conclusion: "module_span(R, restrict_module(M, N), S) = module_span(R, M, S)",
		Abbrev: Abbrev{
			{Name: "combinations", Text: "{module_sum(M.add, M.zero, T, λx:B. a(x) • x) | " +
				"    T:set(B), " +
				"    a:(B → A) | " +
				"    finite(T) ∧ T ⊆ S ∧ (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier)}"},
		},
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], N, S *Expr[Set[B]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"N is a submodule",
				"S lies in N")
			isSubmodule, sInN := given[0], given[1]
			restricted := arg.Have(
				"N with M's operations is a module over R",
				"module_on(R, restrict_module(M, N))",
				By(moduleOn, isSubmodule, submodule.SubmoduleModuleOn))
			sInM := arg.Have(
				"S lies in M, as N does",
				"S ⊆ M.carrier",
				By(
					sInN,
					submodule.SubmoduleSubset.Read(isSubmodule),
					set_order.SubsetTrans.At(S, N, arg.TermAs[Set[B]]("M.carrier"))))
			arg.Show(
				"in both modules the span of S is the set of its finite combinations",
				CalcEq(
					Leg(
						arg.TermAs[Set[B]]("«combinations»"),
						"S lies in N, the restriction's carrier, whose sums and scalings are M's",
						By(sInN, SpanCombinations.Read(restricted).At(S))),
					FinalLeg(
						"and S lies in M",
						By(sInM, SpanCombinations.Read(moduleOn).At(S))),
				))
		}),
})}

// SpanningRestrict — a set spans a submodule N, with M's operations,
// exactly when it lies in N and spans N in M: a set lies in its span, and
// for a set inside N the span is the same in the restriction as in M
// (SpanRestrict).
var SpanningRestrict = spanningRestrictThm{family.Add(registry.ProofEntry{
	Name: "SpanningRestrict",
	Key:  "prop_6bd5ce73636ec524",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N E:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
		},
		Conclusion: "module_span(R, restrict_module(M, N), E) = N ⇔ E ⊆ N ∧ module_span(R, M, E) = N",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], N, E *Expr[Set[B]], sub Fact) {
			R, restricted := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("restrict_module(M, N)")
			inRestriction := arg.TermAs[Set[B]]("module_span(R, restrict_module(M, N), E)")
			sameSpan := SpanRestrict.Read(moduleOn).At(N, E)
			arg.Iff()
			arg.Forward(
				"a set spanning N in the restriction lies in its span, N, and its span in M is the same",
				func(b *Argument, spans Fact) {
					inN := b.Simplified(submodule.SubsetSpan.At(R, restricted, E), Fwd(spans))
					inM := b.Have(
						"its span in M is its span in the restriction, which is N",
						"module_span(R, M, E) = N",
						CalcEq(
							Leg(
								inRestriction,
								"E lying in N, the span is the same in the restriction",
								By(Normalized, sameSpan, sub, inN)),
							FinalLeg(
								"which is N",
								By(spans)),
						))
					b.Show(
						"E lies in N and spans it in M",
						By(inN, inM))
				})
			arg.Backward(
				"a set inside N spanning N in M spans it in the restriction, where its span is the same",
				func(b *Argument, both Fact) {
					b.Show(
						"the span in the restriction is the span in M, which is N",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("module_span(R, M, E)"),
								"E lying in N, the span is the same in M",
								By(sameSpan, sub, both)),
							FinalLeg(
								"which is N",
								By(both)),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Independence, over any ring
// ---------------------------------------------------------------------------

// IndependentSubset — a subset of an independent set is independent: its
// combinations are combinations of the larger set.
var IndependentSubset = independentSubsetThm{family.Add(registry.ProofEntry{
	Name: "IndependentSubset",
	Key:  "prop_7cd367f373f173de",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S T:set(B).",
		Hypotheses: []string{
			"module_independent(R, M, S)",
			"T ⊆ S",
		},
		Conclusion: "module_independent(R, M, T)",
	},
		func(
			arg *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			S, T *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"S is independent",
				"T lies in S")
			independent, tInS := given[0], given[1]
			tInM := arg.Have(
				"T lies in S, which, being independent, lies in M",
				"T ⊆ M.carrier",
				By(
					tInS,
					IndependentInCarrier.Read(independent),
					set_order.SubsetTrans.At(T, S, arg.TermAs[Set[B]]("M.carrier"))))
			vanishing := arg.Have(
				"a vanishing combination over a finite part of T has every coefficient R.zero",
				Statement{
					Binders: "∀U:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(U)",
						"U ⊆ T",
						"∀x:B. x ∈ U ⇒ a(x) ∈ R.carrier",
						"module_sum(M.add, M.zero, U, λx:B. a(x) • x) = M.zero",
					},
					Conclusion: "∀x:B. x ∈ U ⇒ a(x) = R.zero",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[Set[B]]("U")
					a := b.FixAs[Fun[B, A]]("a")
					combination := b.Assume()
					uInS := b.Have(
						"U lies in T, which lies in S",
						"U ⊆ S",
						By(combination, tInS, set_order.SubsetTrans.At(U, T, S)))
					b.Show(
						"so the combination is one over a finite part of S, where only the zero one vanishes",
						By(combination, uInS, IndependentVanishingCombination.Read(independent).AsFact().At(U, a)))
				}))
			arg.Show(
				"T lies in M and only its zero combination vanishes, which is its independence",
				By(tInM, vanishing, ModuleIndependentDef.At(R, M, T)))
		}),
})}

// IndependentRestrict — a set is independent in M restricted to N ⊆
// M.carrier exactly when it lies in N and is independent in M: the
// restriction's sums and scalings are M's, so the two independences ask
// the same of the combinations of E, and differ only in the carrier E must
// lie in, N on the left and M.carrier on the right, which E ⊆ N ⊆
// M.carrier reconciles.
var IndependentRestrict = independentRestrictThm{family.Add(registry.ProofEntry{
	Name: "IndependentRestrict",
	Key:  "prop_4fd6d09d2de52f61",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N E:set(B).",
		Hypotheses: []string{
			"N ⊆ M.carrier",
		},
		Conclusion: "module_independent(R, restrict_module(M, N), E) ⇔ E ⊆ N ∧ module_independent(R, M, E)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N, E *Expr[Set[B]], nInM Fact) {
			a.Show(
				"unfolded, both sides ask the same of the combinations of E, and E ⊆ N ⊆ M.carrier",
				Unfold(ModuleIndependentDef),
				By(nInM, set_order.SubsetTrans.At(E, N, a.TermAs[Set[B]]("M.carrier"))))
		}),
})}

// BasisRestrict — a set is a basis of a submodule N, with M's operations,
// exactly when it is independent in M and spans N there. Either way the
// set lies in N: a basis of N in its carrier, a set spanning N in its
// span. And for a set inside N independence and the span are the same
// in the restriction as in M (IndependentRestrict, SpanRestrict).
var BasisRestrict = basisRestrictThm{family.Add(registry.ProofEntry{
	Name: "BasisRestrict",
	Key:  "prop_55ed52ab0fe143b9",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N E:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
		},
		Conclusion: "module_basis(R, restrict_module(M, N), E) ⇔ " +
			"module_independent(R, M, E) ∧ module_span(R, M, E) = N",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], N, E *Expr[Set[B]], sub Fact) {
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			nInM := arg.Have(
				"N lies in M",
				"N ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(sub)))
			basisDef := ModuleBasisDef.At(R, arg.TermAs[ModuleOps[A, B]]("restrict_module(M, N)"), E)
			independence := IndependentRestrict.At(R, M, N, E)
			sameSpan := SpanRestrict.Read(moduleOn).At(N, E)
			arg.Iff()
			arg.Forward(
				"a basis of N lies in N, so it is independent in M and spans N there as in the restriction",
				func(b *Argument, basis Fact) {
					b.Show(
						"E is independent in M and its span in M is its span in N, which is N",
						By(Normalized, basis, basisDef, independence, nInM, sameSpan, sub))
				})
			arg.Backward(
				"a set independent in M spanning N lies in its span N, "+
					"so it is independent in the restriction and spans N there",
				func(b *Argument, both Fact) {
					b.Show(
						"E lies in N, where its independence and its span are those in M",
						By(Normalized, both, basisDef, independence, nInM, sameSpan, sub, submodule.SubsetSpan.At(R, M, E)))
				})
		}),
})}

// IndependentEmpty — the empty set is independent: its one combination
// has no coefficient.
var IndependentEmpty = independentEmptyThm{family.Add(registry.ProofEntry{
	Name: "IndependentEmpty",
	Key:  "prop_1ca37fbd21fcc6b8",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). module_independent(R, M, ∅)",
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]]) {
			a.Show(
				"∅ lies in M, and a part T of ∅ has no member x, so no coefficient a(x) is constrained",
				BySets(ModuleIndependentDef.At(R, M, a.TermAs[Set[B]]("∅"))))
		}),
})}

// IndependentPair — two distinct members u and v of M are independent
// exactly when c • u + d • v = M.zero only at c = d = R.zero. A
// combination over {u, v} with the coefficient c at u and d at v is
// c • u + d • v (CombinationPair); and a combination over a part T of
// {u, v}, its coefficients extended by zero to both
// (CombinationExtendByZero), is such a sum.
var IndependentPair = independentPairThm{family.Add(registry.ProofEntry{
	Name: "IndependentPair",
	Key:  "prop_b2c46514bc5ddbb9",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀u v:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
			"v ∈ M.carrier",
			"u ≠ v",
		},
		Conclusion: "module_independent(R, M, {u, v}) ⇔ " +
			"∀c d:A. c ∈ R.carrier ∧ d ∈ R.carrier ∧ c • u + d • v = M.zero ⇒ c = R.zero ∧ d = R.zero",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], u, v *Expr[B], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"u lies in M",
				"so does v",
				"u is not v")
			uIn, vIn, apart := parts[0], parts[1], parts[2]
			um, vm := arg.MemberOf[on.M](u, uIn), arg.MemberOf[on.M](v, vIn)
			pair, single := arg.TermAs[Set[B]]("{u, v}"), arg.TermAs[Set[B]]("{v}")
			zeroIn := comm_ring.ZeroIn.Read(module.RingOn.Read(moduleOn))
			pairIn := arg.Have(
				"u and v lie in M",
				"{u, v} ⊆ M.carrier",
				Simp(Fwd(set_order.InsertSubset), Fwd(set_order.EmptySubset)),
				By(uIn, vIn))
			finitePair := arg.Have(
				"{u, v} is finite",
				"finite({u, v})",
				By(finite_set.FiniteInsert.At(u, single), finite_set.FiniteSing.At(v)))
			arg.Iff()
			arg.Forward(
				"an independent pair has only the zero combination",
				func(b *Argument, independent Fact) {
					b.FixAs[A]("c")
					b.FixAs[A]("d")
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"so is d",
						"c • u + d • v = M.zero")
					coefficient := b.TermAs[Fun[B, A]]("λx:B. COND(x = u, c, d)")
					atV := b.Have(
						"v not being u, the coefficient at v is d",
						"COND(v = u, c, d) = d",
						By(apart))
					scalars := b.Have(
						"the coefficients on {u, v} are scalars",
						"∀x:B. x ∈ {u, v} ⇒ COND(x = u, c, d) ∈ R.carrier",
						Simp(Fwd(set_basic.InInsert), Fwd(set_basic.InSing)),
						By(given[0], given[1], atV))
					sum := b.Have(
						"their combination over {u, v} is c • u + d • v, which is zero",
						"module_sum(M.add, M.zero, {u, v}, λx:B. COND(x = u, c, d) • x) = M.zero",
						CalcEq(
							Leg(
								b.TermAs[B]("COND(u = u, c, d) • u + COND(v = u, c, d) • v"),
								"a combination of two distinct members is its two terms",
								By(apart, given[0], given[1], atV, CombinationPair.Read(moduleOn).At(um, vm, coefficient))),
							FinalLeg(
								"which is c • u + d • v",
								atV.Rw(),
								By(given[2])),
						))
					vanishing := IndependentVanishingCombination.Read(independent)
					cZero := b.Have(
						"so the coefficient at u, c, is zero",
						"c = R.zero",
						By(
							finitePair,
							set_order.SubsetRefl.At(pair),
							scalars,
							sum,
							set_basic.InInsert.At(single, u, u),
							vanishing.At(pair, coefficient, u)))
					dZero := b.Have(
						"and so is the coefficient at v, d",
						"d = R.zero",
						By(
							finitePair,
							set_order.SubsetRefl.At(pair),
							scalars,
							sum,
							atV,
							set_basic.InInsert.At(single, u, v),
							set_basic.InSing.At(v, v),
							vanishing.At(pair, coefficient, v)))
					b.Show(
						"both coefficients vanish",
						By(cZero, dZero))
				})
			arg.Backward(
				"only the zero combination makes a pair independent",
				func(b *Argument, only Fact) {
					vanishing := b.Have(
						"a combination over a part of {u, v} vanishes only with its coefficients",
						Statement{
							Binders: "∀T:set(B). ∀a:(B → A).",
							Hypotheses: []string{
								"finite(T)",
								"T ⊆ {u, v}",
								"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
								"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero",
							},
							Conclusion: "∀x:B. x ∈ T ⇒ a(x) = R.zero",
						},
						Derive(func(d *Argument) {
							T := d.FixAs[Set[B]]("T")
							a := d.FixAs[Fun[B, A]]("a")
							hyps := d.Conjuncts(
								d.Assume(),
								"T is finite",
								"T lies in {u, v}",
								"its coefficients are scalars",
								"and the combination over T vanishes")
							tInPair, coefficientsIn, vanishes := hyps[1], hyps[2], hyps[3]
							extended := d.TermAs[Fun[B, A]]("λx:B. COND(x ∈ T, a(x), R.zero)")
							extend := d.Have(
								"over {u, v}, with the coefficients extended by zero, the combination is the same",
								"module_sum(M.add, M.zero, {u, v}, λx:B. COND(x ∈ T, a(x), R.zero) • x) = "+
									"module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
								By(
									finitePair,
									tInPair,
									pairIn,
									coefficientsIn,
									CombinationExtendByZero.Read(moduleOn).At(T, pair, a)))
							extendedIn := d.Have(
								"the extended coefficients are scalars",
								"∀x:B. COND(x ∈ T, a(x), R.zero) ∈ R.carrier",
								d.ForEach(func(x *Expr[B]) Action {
									return By(coefficientsIn.At(x), zeroIn)
								}))
							split := d.Have(
								"which is its term at u plus its term at v",
								"module_sum(M.add, M.zero, {u, v}, λx:B. COND(x ∈ T, a(x), R.zero) • x) = "+
									"COND(u ∈ T, a(u), R.zero) • u + COND(v ∈ T, a(v), R.zero) • v",
								By(apart, extendedIn.At(u), extendedIn.At(v), CombinationPair.Read(moduleOn).At(um, vm, extended)))
							zeros := d.Have(
								"so both extended coefficients are zero",
								"COND(u ∈ T, a(u), R.zero) = R.zero ∧ COND(v ∈ T, a(v), R.zero) = R.zero",
								By(
									extendedIn.At(u),
									extendedIn.At(v),
									vanishes,
									extend,
									split,
									only.At(d.TermAs[A]("COND(u ∈ T, a(u), R.zero)"), d.TermAs[A]("COND(v ∈ T, a(v), R.zero)"))))
							d.FixAs[B]("x")
							xIn := d.Assume()
							d.Show(
								"a member x of T is u or v, where its coefficient is the extended one, zero",
								BySets(xIn, tInPair, zeros))
						}))
					b.Show(
						"so {u, v}, inside M, is independent",
						Unfold(ModuleIndependentDef),
						By(pairIn, vanishing))
				})
		}),
})}

// RegularModuleBasis — a commutative ring is free of rank one over
// itself, with the basis {one}: every x of the ring is x * one, a
// multiple of one inside the submodule the span of {one} is, and a
// combination over a part T of {one} is its one term p(one) * one =
// p(one), which vanishes only when its coefficient does.
var RegularModuleBasis = regularModuleBasisThm{family.Add(registry.ProofEntry{
	Name: "RegularModuleBasis",
	Key:  "prop_b0e4559e2fd0f389",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A).",
		Conclusion: "module_basis(R, regular_module(R), {R.one})",
		Abbrev: Abbrev{
			{Name: "regularModuleSpan", Text: "module_span(R, regular_module(R), {R.one})"},
		},
	},
		func(a *Argument, R comm_ring.CommRingFact[on.R]) {
			regular := module.RegularModuleOn.Read(R)
			mulMonoid := comm_ring.MulMonoidOn.Read(R)
			scalars := a.TermAs[RingOps[A]]("R")
			M := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			ring, one := a.TermAs[Set[A]]("R.carrier"), a.TermAs[A]("R.one")
			single, span := a.TermAs[Set[A]]("{R.one}"), a.TermAs[Set[A]]("«regularModuleSpan»")

			oneIn := a.Have(
				"one lies in the ring",
				"R.one ∈ R.carrier",
				By(comm_ring.OneIn.Read(R)))
			singleIn := a.Have(
				"so {one} lies in it",
				"{R.one} ⊆ R.carrier",
				By(oneIn, set_order.SingSubset.At(ring, one)))

			// {one} spans the ring.
			spanIn := a.Have(
				"the span of {one} lies in the ring, a submodule holding one",
				"«regularModuleSpan» ⊆ R.carrier",
				By(
					singleIn,
					submodule.CarrierSubmodule.Read(regular),
					submodule.SpanLeast.At(scalars, M, single, ring)))
			spanSubmodule := a.Have(
				"the span of {one} is a submodule",
				"submodule(R, regular_module(R), «regularModuleSpan»)",
				By(singleIn, submodule.SpanSubmodule.Read(regular).At(single)))
			ringInSpan := a.Have(
				"every x of the ring is x * one, a multiple of one inside the submodule",
				"R.carrier ⊆ «regularModuleSpan»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					xm := b.MemberOf[on.R](x, b.Assume())
					b.Show(
						"x * one lies in the span, and x * one is x",
						By(
							submodule.SubsetSpan.At(scalars, M, single),
							set_order.SingSubset.At(span, one),
							spanSubmodule,
							submodule.SubmoduleSmul.At(scalars, M, span, x, one),
							comm_monoid.RightIdentityOn.Read(mulMonoid).At(xm)))
				}))
			spans := a.Have(
				"so the span of {one} is the ring",
				"«regularModuleSpan» = R.carrier",
				By(spanIn, ringInSpan, set_order.SubsetAntisym.At(span, ring)))

			// {one} is independent.
			vanishing := a.Have(
				"a combination over a part T of {one} is its one term "+
					"p(one) * one = p(one), so it vanishes only with p(one)",
				"∀T:set(A). ∀p:(A → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ {R.one} ∧ "+
					"    (∀x:A. x ∈ T ⇒ p(x) ∈ R.carrier) ∧ "+
					"    module_sum(R.add, R.zero, T, λx:A. p(x) * x) = R.zero ⇒ "+
					"    ∀x:A. x ∈ T ⇒ p(x) = R.zero",
				Derive(func(b *Argument) {
					T := b.FixAs[Set[A]]()
					b.FixAs[Fun[A, A]]()
					given := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T lies in {one}",
						"its coefficients are scalars",
						"the combination vanishes")
					finiteT, inSingle, scalars, vanishes := given[0], given[1], given[2], given[3]
					members := b.Have(
						"every member of T is one",
						"∀y:A. y ∈ T ⇒ y = R.one",
						By(inSingle, set_basic.SubsetDef, set_basic.InSing))
					x := b.FixAs[A]()
					xIn := b.Assume()
					xIsOne := b.Have(
						"x is one",
						"x = R.one",
						By(members.At(x), xIn))
					oneInT := b.Have(
						"so one lies in T",
						"R.one ∈ T",
						xIsOne.RwRev(),
						By(xIn))
					terms := b.Have(
						"each term p(y) * y lies in the ring",
						"∀y:A. y ∈ T ⇒ p(y) * y ∈ R.carrier",
						Derive(func(d *Argument) {
							y := d.FixAs[A]()
							yInT := d.Assume()
							inRing := d.Have(
								"y is one, which lies in the ring",
								"y ∈ R.carrier",
								GroupPremises(yInT, members.At(y)).Rw(),
								By(oneIn))
							coefficientY := d.MemberOf[on.R](d.TermAs[A]("p(y)"), GroupPremises(yInT, scalars.At(y)))
							d.Show(
								"a product of members of the ring",
								By(comm_ring.MulIn.Read(R).At(coefficientY, d.MemberOf[on.R](y, inRing))))
						}))
					others := b.Have(
						"T has no term besides the one at one",
						"∀y:A. y ∈ T ∧ y ≠ R.one ⇒ p(y) * y = R.zero",
						Derive(func(d *Argument) {
							y := d.FixAs[A]()
							given := d.Conjuncts(
								d.Assume(),
								"y lies in T",
								"y is not one")
							d.Show(
								"no such y: every member of T is one",
								By(members.At(y), given[0], given[1]))
						}))
					term := b.Have(
						"so the combination is its one term",
						"module_sum(R.add, R.zero, T, λx:A. p(x) * x) = p(R.one) * R.one",
						By(
							finiteT,
							oneInT,
							terms,
							others,
							module.ModuleSumSingle.Read(regular).At(T, one, b.TermAs[Fun[A, A]]("λx:A. p(x) * x"))))
					coefficient := b.MemberOf[on.R](b.TermAs[A]("p(R.one)"), GroupPremises(oneInT, scalars.At(one)))
					b.Show(
						"p(x) is p(one), its own multiple p(one) * one, the combination, which vanishes",
						xIsOne.Rw(),
						CalcEq(
							Leg(
								b.TermAs[A]("p(R.one) * R.one"),
								"one is a unit for the product",
								By(comm_monoid.RightIdentityOn.Read(mulMonoid).At(coefficient))),
							Leg(
								b.TermAs[A]("module_sum(R.add, R.zero, T, λx:A. p(x) * x)"),
								"the combination is its one term",
								By(term)),
							FinalLeg(
								"which vanishes",
								By(vanishes)),
						))
				}))
			independent := a.Have(
				"so {one} is independent",
				"module_independent(R, regular_module(R), {R.one})",
				By(singleIn, vanishing, ModuleIndependentDef))
			a.Show(
				"{one} is independent and spans the ring",
				By(independent, spans, ModuleBasisDef))
		}),
})}

// IndependentZeroNotIn — an independent set over a ring whose one is not
// zero misses the zero vector: one • M.zero is a vanishing combination
// with a nonzero coefficient.
var IndependentZeroNotIn = independentZeroNotInThm{family.Add(registry.ProofEntry{
	Name: "IndependentZeroNotIn",
	Key:  "prop_d4e9c2c8b86f303b",
	Reading: "one ≠ zero is load-bearing: over the zero ring every coefficient " +
		"is zero, every subset of M is independent, and {M.zero} is one.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B).",
		Hypotheses: []string{
			"R.one ≠ R.zero",
			"module_independent(R, M, S)",
		},
		Conclusion: "M.zero ∉ S",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], S *Expr[Set[B]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"R.one is not R.zero",
				"S is independent")
			oneNotZero, independent := given[0], given[1]
			oneIn := arg.Have(
				"R.one is a scalar",
				"R.one ∈ R.carrier",
				By(comm_ring.OneIn.Read(module.RingOn.Read(moduleOn))))
			one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), oneIn)
			zero, single := arg.TermAs[B]("M.zero"), arg.TermAs[Set[B]]("{M.zero}")
			finiteSingle := finite_set.FiniteSing.At(zero)
			terms := arg.Have(
				"the one term over {M.zero} with the coefficient R.one is R.one • M.zero, which is M.zero",
				"∀x:B. x ∈ {M.zero} ⇒ R.one • x = M.zero",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(Normalized, set_basic.InSing.At(x, zero), module.SmulZero.Read(moduleOn).At(one))
				}))
			vanishing := arg.Have(
				"so that combination over {M.zero} vanishes",
				"module_sum(M.add, M.zero, {M.zero}, λx:B. R.one • x) = M.zero",
				By(
					terms,
					finiteSingle,
					module.ModuleSumZero.Read(moduleOn).At(single, arg.TermAs[Fun[B, B]]("λx:B. R.one • x"))))
			zeroInS := arg.SupposeNot()
			oneIsZero := arg.Have(
				"then {M.zero} is a finite part of S, and independence "+
					"makes the coefficient R.one of that combination zero",
				"R.one = R.zero",
				By(
					IndependentVanishingCombination.Read(independent).At(
						single, arg.TermAs[Fun[B, A]]("λx:B. R.one"), zero),
					zeroInS,
					vanishing,
					finiteSingle,
					set_order.SingSubset.At(S, zero),
					set_basic.InSing.At(zero, zero),
					oneIn))
			arg.Show(
				"which contradicts R.one ≠ R.zero",
				By(oneIsZero, oneNotZero))
		}),
})}

// IndependentUniqueCoefficients — two combinations of an independent set
// over one finite part that agree have the same coefficients: the
// combination of b plus the combination of the differences a(x) − b(x)
// is the combination of a, which is b's, so cancelling b's leaves the
// combination of the differences vanishing, and independence makes every
// difference zero.
var IndependentUniqueCoefficients = independentUniqueCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "IndependentUniqueCoefficients",
	Key:  "prop_f72a0276556bd034",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S T:set(B). ∀a b:(B → A). ∀z:B.",
		Hypotheses: []string{
			"module_independent(R, M, S)",
			"finite(T)",
			"T ⊆ S",
			"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier ∧ b(x) ∈ R.carrier",
			"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = module_sum(M.add, M.zero, T, λx:B. b(x) • x)",
			"z ∈ T",
		},
		Conclusion: "a(z) = b(z)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			S, T *Expr[Set[B]],
			a, b *Arrow[B, A],
			hypotheses Fact,
			z *Expr[B],
			zInT Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"S is independent",
				"T is finite",
				"T lies in S",
				"a and b are scalars on T",
				"the combinations of a and b over T agree")
			independent, finT, tInS, scalars, agree := parts[0], parts[1], parts[2], parts[3], parts[4]
			ring, additive := module.RingOn.Read(moduleOn), module.AddGroupOn.Read(moduleOn)
			vecAdd, vecZero := arg.TermAs[Op[B]]("M.add"), arg.TermAs[B]("M.zero")
			difference := arg.TermAs[Fun[B, A]]("λx:B. a(x) - b(x)")
			tInM := arg.Have(
				"T lies in S, which, being independent, lies in M",
				"T ⊆ M.carrier",
				By(
					tInS,
					IndependentInCarrier.Read(independent),
					set_order.SubsetTrans.At(T, S, arg.TermAs[Set[B]]("M.carrier"))))
			differences := arg.Have(
				"each difference a(x) − b(x) is a scalar",
				"∀x:B. x ∈ T ⇒ a(x) - b(x) ∈ R.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(scalars.At(x), comm_ring.SubIn.Read(ring))
				}))
			restored := arg.Have(
				"b(x) plus the difference is a(x)",
				"∀x:B. x ∈ T ⇒ b(x) + (a(x) - b(x)) = a(x)",
				Derive(func(c *Argument) {
					x := c.FixAs[B]("x")
					xInT := c.Assume()
					members := c.Have(
						"a(x) and b(x) are scalars",
						"a(x) ∈ R.carrier ∧ b(x) ∈ R.carrier",
						By(scalars.At(x), xInT))
					c.Show(
						"a regrouping in the ring",
						ByArith(ring, members))
				}))
			termsAgree := arg.Have(
				"so the terms with the added coefficients are a's terms",
				"∀x:B. x ∈ T ⇒ (b(x) + (a(x) - b(x))) • x = a(x) • x",
				arg.ForEach(func(x *Expr[B]) Action { return By(restored.At(x)) }))
			split := arg.Have(
				"the combination of b plus the combination of the differences is the combination of a",
				"module_sum(M.add, M.zero, T, λx:B. b(x) • x) + "+
					"module_sum(M.add, M.zero, T, λx:B. (a(x) - b(x)) • x) = "+
					"module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
				CalcEq(
					Leg(
						arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. (b(x) + (a(x) - b(x))) • x)"),
						"two combinations over T add coefficientwise",
						By(finT, tInM, scalars, differences, CombinationAdd.Read(moduleOn).At(T, b, difference))),
					FinalLeg(
						"and the added coefficients are a's",
						By(
							termsAgree,
							module.ModuleSumCongruence.At(
								vecAdd,
								vecZero,
								T,
								arg.TermAs[Fun[B, B]]("λx:B. (b(x) + (a(x) - b(x))) • x"),
								arg.TermAs[Fun[B, B]]("λx:B. a(x) • x")))),
				))
			inM := arg.Unfolded(tInM, set_basic.SubsetDef)
			sums := arg.Conjuncts(
				arg.Have(
					"both combinations lie in M, finite sums of scaled members of M",
					"module_sum(M.add, M.zero, T, λx:B. b(x) • x) ∈ M.carrier ∧ "+
						"module_sum(M.add, M.zero, T, λx:B. (a(x) - b(x)) • x) ∈ M.carrier",
					By(
						finT,
						inM,
						scalars,
						differences,
						module.SmulIn.Read(moduleOn),
						module.ModuleSumIn.Read(moduleOn))),
				"the combination of b lies in M",
				"the combination of the differences lies in M")
			bSum := arg.MemberOf[on.M](arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. b(x) • x)"), sums[0])
			dSum := arg.MemberOf[on.M](
				arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. (a(x) - b(x)) • x)"), sums[1])
			zero := arg.MemberOf[on.M](vecZero, arg.Have(
				"M.zero lies in M",
				"M.zero ∈ M.carrier",
				By(group.OneIn.Read(additive))))
			vanishes := arg.Have(
				"adding the combination of the differences to b's leaves b's, as adding M.zero does: cancel b's",
				"module_sum(M.add, M.zero, T, λx:B. (a(x) - b(x)) • x) = M.zero",
				By(
					split,
					agree,
					group.LeftCancelOn.Read(additive).At(bSum, dSum, zero),
					group.RightIdentityOn.Read(additive).At(bSum)))
			differenceAtZ := arg.Have(
				"S is independent, so the difference at z is zero",
				"a(z) - b(z) = R.zero",
				By(
					IndependentVanishingCombination.Read(independent).At(T, difference, z),
					finT,
					tInS,
					differences,
					vanishes,
					zInT))
			scalarsAtZ := arg.Have(
				"a(z) and b(z) are scalars",
				"a(z) ∈ R.carrier ∧ b(z) ∈ R.carrier",
				By(scalars.At(z), zInT))
			arg.Show(
				"a(z) is b(z) plus a zero difference",
				CalcEq(
					Leg(
						arg.TermAs[A]("b(z) + (a(z) - b(z))"),
						"b(z) plus the difference is a(z)",
						By(restored.At(z), zInT)),
					FinalLeg(
						"and the difference vanishes",
						ByArith(ring, differenceAtZ, scalarsAtZ)),
				))
		}),
})}

// IndependentChainUnion — the union of a chain of independent sets is
// independent: a finite part of the union lies in one member of the
// chain.
var IndependentChainUnion = independentChainUnionThm{family.Add(registry.ProofEntry{
	Name: "IndependentChainUnion",
	Key:  "prop_18ffcf5e8dd08fbb",
	Reading: "An empty family has the empty union, which " +
		"is independent, so the chain need not be nonempty.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀F:set(set(B)).",
		Hypotheses: []string{
			"∀S:set(B). S ∈ F ⇒ module_independent(R, M, S)",
			"∀S T:set(B). S ∈ F ∧ T ∈ F ⇒ S ⊆ T ∨ T ⊆ S",
		},
		Conclusion: "module_independent(R, M, ⋃F)",
	},
		func(
			arg *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			F *Expr[Set[Set[B]]],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"every member of F is independent",
				"F is a chain")
			independent, chain := given[0], given[1]
			members := arg.Have(
				"each member of F, being independent, lies in M",
				"∀S:set(B). S ∈ F ⇒ S ⊆ M.carrier",
				arg.ForEach(func(S *Expr[Set[B]]) Action {
					return By(independent.At(S), IndependentInCarrier.At(R, M, S))
				}))
			vanishing := arg.Have(
				"a vanishing combination over a finite part of ⋃F has every coefficient zero",
				Statement{
					Binders: "∀T:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ ⋃F",
						"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
						"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero",
					},
					Conclusion: "∀x:B. x ∈ T ⇒ a(x) = R.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[B]]("T")
					a := b.FixAs[Fun[B, A]]("a")
					combination := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T lies in ⋃F",
						"a is a scalar on T",
						"the combination vanishes")
					finiteT, tInUnion, scalars, vanishes :=
						combination[0], combination[1], combination[2], combination[3]
					x := b.FixAs[B]("x")
					xInT := b.Assume()
					nonempty := b.Have(
						"x lies in ⋃F, so F has a member",
						"¬(F = ∅)",
						BySets(xInT, tInUnion))
					S, held := b.ObtainAs[Set[B]](
						"the chain F covers the finite T, so one member S of F holds all of it",
						"∃S:set(B). S ∈ F ∧ T ⊆ S",
						By(finiteT, tInUnion, nonempty, chain, finite_set.FiniteSubsetUnionsChain.At(F, T)))
					member := b.Conjuncts(
						held,
						"S is a member of F",
						"S holds T")
					sInF, tInS := member[0], member[1]
					independentS := b.Have(
						"S, a member of F, is independent",
						"module_independent(R, M, S)",
						By(sInF, independent.At(S)))
					b.Show(
						"the combination is one over a finite part of S, so its coefficient at x is zero",
						By(
							finiteT,
							tInS,
							scalars,
							vanishes,
							xInT,
							IndependentVanishingCombination.Read(independentS).At(T, a, x)))
				}))
			arg.Show(
				"⋃F lies in M and only the zero combination of it vanishes",
				By(
					members,
					set_order.UnionsSubset,
					vanishing,
					ModuleIndependentDef.At(R, M, arg.TermAs[Set[B]]("⋃F"))))
		}),
})}

// IndependentUnion — two independent sets whose spans meet only in zero
// have an independent union: a vanishing combination over U ⊆ S ∪ T is
// the sum of its parts over U ∩ S and over U ∖ S ⊆ T, so the first part
// is the negative of the second and lies in both spans; it is M.zero,
// and then so is the second, and the independence of S and of T clears
// the coefficients of each part.
var IndependentUnion = independentUnionThm{family.Add(registry.ProofEntry{
	Name: "IndependentUnion",
	Key:  "prop_e2326fade46c2243",
	Reading: "S and T need not be disjoint: a member of both lies in both " +
		"spans, so it is M.zero, and a combination over a finite part of S ∪ " +
		"T still splits along its part in S and the rest, which lies in T.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S T:set(B).",
		Hypotheses: []string{
			"module_independent(R, M, S)",
			"module_independent(R, M, T)",
			"module_span(R, M, S) ∩ module_span(R, M, T) ⊆ {M.zero}",
		},
		Conclusion: "module_independent(R, M, S ∪ T)",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], S, T *Expr[Set[B]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"S is independent",
				"T is independent",
				"the spans of S and T meet only in zero")
			independentS, independentT, meet := given[0], given[1], given[2]
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			carrier, union := arg.TermAs[Set[B]]("M.carrier"), arg.TermAs[Set[B]]("S ∪ T")
			additive := module.AddGroupOn.Read(moduleOn)
			sInM := arg.Have(
				"S, being independent, lies in M",
				"S ⊆ M.carrier",
				By(IndependentInCarrier.Read(independentS)))
			tInM := arg.Have(
				"and so does T",
				"T ⊆ M.carrier",
				By(IndependentInCarrier.Read(independentT)))
			unionInM := arg.Have(
				"so S ∪ T lies in M",
				"S ∪ T ⊆ M.carrier",
				By(sInM, tInM, set_order.UnionSubset.At(S, T, carrier)))
			spanS := arg.Have(
				"the span of S is a submodule of M",
				"submodule(R, M, module_span(R, M, S))",
				By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S)))
			spanT := arg.Have(
				"and so is the span of T",
				"submodule(R, M, module_span(R, M, T))",
				By(tInM, submodule.SpanSubmodule.Read(moduleOn).At(T)))

			// A vanishing combination over U splits along U ∩ S and U ∖ S ⊆ T;
			// its part over U ∩ S is the negative of the other, so it lies in
			// both spans and is M.zero, and then so is the other.
			vanishing := arg.Have(
				"a vanishing combination over a finite part of S ∪ T has every coefficient R.zero",
				Statement{
					Binders: "∀U:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(U)",
						"U ⊆ S ∪ T",
						"∀x:B. x ∈ U ⇒ a(x) ∈ R.carrier",
						"module_sum(M.add, M.zero, U, λx:B. a(x) • x) = M.zero",
					},
					Conclusion: "∀x:B. x ∈ U ⇒ a(x) = R.zero",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[Set[B]]("U")
					a := b.FixAs[Fun[B, A]]("a")
					combination := b.Conjuncts(
						b.Assume(),
						"U is finite",
						"U lies in S ∪ T",
						"a is a scalar on U",
						"the combination vanishes")
					inS, outS := b.TermAs[Set[B]]("U ∩ S"), b.TermAs[Set[B]]("U ∖ S")
					finiteIn := b.Have(
						"U ∩ S is finite",
						"finite(U ∩ S)",
						By(combination[0], finite_set.FiniteInter.At(U, S)))
					finiteOut := b.Have(
						"and so is U ∖ S",
						"finite(U ∖ S)",
						By(combination[0], finite_set.FiniteDiff.At(U, S)))
					inSInS := b.Have(
						"U ∩ S lies in S",
						"U ∩ S ⊆ S",
						BySets())
					inUnion := b.Unfolded(combination[1], set_basic.SubsetDef)
					outInT := b.Have(
						"and U ∖ S in T, U lying in S ∪ T",
						"U ∖ S ⊆ T",
						Simp(Fwd(set_basic.SubsetDef)),
						b.ForEach(func(x *Expr[B]) Action { return BySets(inUnion.At(x)) }))
					scalarsIn := b.Have(
						"a is a scalar on U ∩ S",
						"∀x:B. x ∈ U ∩ S ⇒ a(x) ∈ R.carrier",
						BySets(combination[2]))
					scalarsOut := b.Have(
						"and on U ∖ S",
						"∀x:B. x ∈ U ∖ S ⇒ a(x) ∈ R.carrier",
						BySets(combination[2]))
					uInM := b.Unfolded(b.Have(
						"U lies in M",
						"U ⊆ M.carrier",
						By(combination[1], unionInM, set_order.SubsetTrans.At(U, union, carrier))), set_basic.SubsetDef)
					terms := b.Have(
						"each term a(x) • x over U lies in M",
						"∀x:B. x ∈ U ⇒ a(x) • x ∈ M.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(uInM.At(x), combination[2].At(x), module.SmulIn.Read(moduleOn))
						}))
					partsTerms := b.Have(
						"so does each term over U ∩ S or over U ∖ S",
						"∀x:B. x ∈ U ∩ S ∨ x ∈ U ∖ S ⇒ a(x) • x ∈ M.carrier",
						b.ForEach(func(x *Expr[B]) Action { return BySets(terms.At(x)) }))
					partition := b.Conjuncts(
						b.Have(
							"U is U ∩ S together with U ∖ S, which do not meet",
							"(U ∩ S) ∪ (U ∖ S) = U ∧ disjoint(U ∩ S, U ∖ S)",
							BySets()),
						"U is the union of its two parts",
						"the two parts do not meet")
					split := b.Have(
						"the combination over U is the sum of its parts over U ∩ S and over U ∖ S",
						"module_sum(M.add, M.zero, U, λx:B. a(x) • x) = "+
							"module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x) + "+
							"module_sum(M.add, M.zero, U ∖ S, λx:B. a(x) • x)",
						CalcEq(
							Leg(
								b.TermAs[B]("module_sum(M.add, M.zero, (U ∩ S) ∪ (U ∖ S), λx:B. a(x) • x)"),
								"U is the union of its two parts",
								partition[0].Rw(),
								Basic()),
							FinalLeg(
								"which do not meet",
								By(
									finiteIn,
									finiteOut,
									partition[1],
									partsTerms,
									module.ModuleSumDisjointUnion.Read(moduleOn).At(inS, outS, b.TermAs[Fun[B, B]]("λx:B. a(x) • x")))),
						))

					firstIn := b.Have(
						"the part over U ∩ S is a combination of S, so it lies in the span of S",
						"module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x) ∈ module_span(R, M, S)",
						Simp(Fwd(SpanMembership.Read(moduleOn))),
						Derive(func(c *Argument) {
							c.Take(inS)
							c.Take(a)
							c.Show(
								"U ∩ S is a finite part of S on which a is a scalar",
								By(finiteIn, inSInS, scalarsIn))
						}))
					secondIn := b.Have(
						"the part over U ∖ S is a combination of T, so it lies in the span of T",
						"module_sum(M.add, M.zero, U ∖ S, λx:B. a(x) • x) ∈ module_span(R, M, T)",
						Simp(Fwd(SpanMembership.Read(moduleOn))),
						Derive(func(c *Argument) {
							c.Take(outS)
							c.Take(a)
							c.Show(
								"U ∖ S is a finite part of T on which a is a scalar",
								By(finiteOut, outInT, scalarsOut))
						}))
					firstPart, secondPart :=
						b.TermAs[B]("module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x)"),
						b.TermAs[B]("module_sum(M.add, M.zero, U ∖ S, λx:B. a(x) • x)")
					first := b.MemberOf[on.M](firstPart,
						b.Have(
							"the part over U ∩ S lies in M, as the span of S does",
							"module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x) ∈ M.carrier",
							BySets(firstIn, submodule.SubmoduleSubset.Read(spanS))))
					second := b.MemberOf[on.M](secondPart,
						b.Have(
							"and the part over U ∖ S, as the span of T does",
							"module_sum(M.add, M.zero, U ∖ S, λx:B. a(x) • x) ∈ M.carrier",
							BySets(secondIn, submodule.SubmoduleSubset.Read(spanT))))
					opposite := b.Have(
						"the two parts add to the vanishing combination, so the first is the negative of the second",
						"module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x) = "+
							"-module_sum(M.add, M.zero, U ∖ S, λx:B. a(x) • x)",
						By(split, combination[3], group.InvUniqueOn.Read(additive).At(first, second)))
					firstInT := b.Have(
						"so the part over U ∩ S lies in the span of T as well, a submodule holding the second part",
						"module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x) ∈ module_span(R, M, T)",
						By(opposite, submodule.SubmoduleNeg.Read(spanT).At(proof.MemberOf(secondPart, secondIn))))
					firstZero := b.Have(
						"the spans meet only in zero, so the part over U ∩ S is M.zero",
						"module_sum(M.add, M.zero, U ∩ S, λx:B. a(x) • x) = M.zero",
						BySets(meet, firstIn, firstInT))
					secondZero := b.Have(
						"M.zero plus the part over U ∖ S is the vanishing combination, so that part is M.zero too",
						"module_sum(M.add, M.zero, U ∖ S, λx:B. a(x) • x) = M.zero",
						By(split, combination[3], firstZero, group.LeftIdentityOn.Read(additive).At(second)))
					clearedIn := b.Have(
						"S being independent, a vanishes on U ∩ S",
						"∀x:B. x ∈ U ∩ S ⇒ a(x) = R.zero",
						By(
							finiteIn,
							inSInS,
							scalarsIn,
							firstZero,
							IndependentVanishingCombination.Read(independentS).AsFact().At(inS, a)))
					clearedOut := b.Have(
						"and T being independent, a vanishes on U ∖ S",
						"∀x:B. x ∈ U ∖ S ⇒ a(x) = R.zero",
						By(
							finiteOut,
							outInT,
							scalarsOut,
							secondZero,
							IndependentVanishingCombination.Read(independentT).AsFact().At(outS, a)))
					b.Show(
						"every member of U lies in U ∩ S or in U ∖ S",
						b.ForEach(func(x *Expr[B]) Action {
							return BySets(clearedIn.At(x), clearedOut.At(x))
						}))
				}))
			arg.Show(
				"S ∪ T lies in M and only its zero combination vanishes, which is its independence",
				By(unionInM, vanishing, ModuleIndependentDef.At(R, M, union)))
		}),
})}

// IndependentSpansMeet — the spans of two disjoint parts of an
// independent set meet only in zero, the converse of IndependentUnion: a
// vector of both spans is a combination over a finite U₁ ⊆ S and one over
// a finite U₂ ⊆ T; extended by zero, both are combinations over U₁ ∪ U₂,
// a finite part of the independent S ∪ T, so their coefficients agree
// there, and on U₁, which U₂ does not meet, the second is zero, so the
// first combination has every term zero.
var IndependentSpansMeet = independentSpansMeetThm{family.Add(registry.ProofEntry{
	Name: "IndependentSpansMeet",
	Key:  "prop_56eb20d346864de7",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S T:set(B).",
		Hypotheses: []string{
			"module_independent(R, M, S ∪ T)",
			"S ∩ T = ∅",
		},
		Conclusion: "module_span(R, M, S) ∩ module_span(R, M, T) ⊆ {M.zero}",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], S, T *Expr[Set[B]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"S ∪ T is independent",
				"S and T do not meet")
			independent, apart := given[0], given[1]
			carrier, union := arg.TermAs[Set[B]]("M.carrier"), arg.TermAs[Set[B]]("S ∪ T")
			zeroIn := comm_ring.ZeroIn.Read(module.RingOn.Read(moduleOn))
			unionInM := arg.Have(
				"S ∪ T, being independent, lies in M",
				"S ∪ T ⊆ M.carrier",
				By(IndependentInCarrier.Read(independent)))
			parts := arg.Conjuncts(
				arg.Have(
					"so S and T lie in M",
					"S ⊆ M.carrier ∧ T ⊆ M.carrier",
					By(unionInM, set_order.UnionSubset.At(S, T, carrier))),
				"S lies in M",
				"T lies in M")
			sInM, tInM := parts[0], parts[1]

			common := arg.Have(
				"a vector of both spans is M.zero",
				"∀v:B. v ∈ module_span(R, M, S) ∧ v ∈ module_span(R, M, T) ⇒ v = M.zero",
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					inSpans := b.Conjuncts(
						b.Assume(),
						"v lies in the span of S",
						"v lies in the span of T")
					U1, a1, first := b.Obtain2As[Set[B], Fun[B, A]](
						"v is a combination over a finite U₁ ⊆ S",
						"∃U₁:set(B). ∃a₁:(B → A). "+
							"    finite(U₁) ∧ "+
							"    U₁ ⊆ S ∧ "+
							"    (∀x:B. x ∈ U₁ ⇒ a₁(x) ∈ R.carrier) ∧ "+
							"    v = module_sum(M.add, M.zero, U₁, λx:B. a₁(x) • x)",
						By(inSpans[0], sInM, SpanMembership.Read(moduleOn).At(S, v)))
					U2, a2, second := b.Obtain2As[Set[B], Fun[B, A]](
						"and a combination over a finite U₂ ⊆ T",
						"∃U₂:set(B). ∃a₂:(B → A). "+
							"    finite(U₂) ∧ "+
							"    U₂ ⊆ T ∧ "+
							"    (∀x:B. x ∈ U₂ ⇒ a₂(x) ∈ R.carrier) ∧ "+
							"    v = module_sum(M.add, M.zero, U₂, λx:B. a₂(x) • x)",
						By(inSpans[1], tInM, SpanMembership.Read(moduleOn).At(T, v)))
					onFirst := b.Conjuncts(
						first,
						"U₁ is finite",
						"U₁ lies in S",
						"a₁ is a scalar on U₁",
						"v is the combination of a₁ over U₁")
					onSecond := b.Conjuncts(
						second,
						"U₂ is finite",
						"U₂ lies in T",
						"a₂ is a scalar on U₂",
						"v is the combination of a₂ over U₂")

					// Both combinations, extended by zero, over U₁ ∪ U₂.
					both := b.TermAs[Set[B]]("U₁ ∪ U₂")
					extended1 := b.TermAs[Fun[B, A]]("λx:B. COND(x ∈ U₁, a₁(x), R.zero)")
					extended2 := b.TermAs[Fun[B, A]]("λx:B. COND(x ∈ U₂, a₂(x), R.zero)")
					finBoth := b.Have(
						"U₁ ∪ U₂ is finite",
						"finite(U₁ ∪ U₂)",
						By(onFirst[0], onSecond[0], finite_set.FiniteUnion.At(U1, U2)))
					bothInUnion := b.Have(
						"and lies in S ∪ T",
						"U₁ ∪ U₂ ⊆ S ∪ T",
						BySets(onFirst[1], onSecond[1]))
					bothInM := b.Have(
						"so in M",
						"U₁ ∪ U₂ ⊆ M.carrier",
						By(bothInUnion, unionInM, set_order.SubsetTrans.At(both, union, carrier)))
					scalars := b.Have(
						"the coefficients extended by zero are scalars",
						"∀x:B. COND(x ∈ U₁, a₁(x), R.zero) ∈ R.carrier ∧ COND(x ∈ U₂, a₂(x), R.zero) ∈ R.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(onFirst[2].At(x), onSecond[2].At(x), zeroIn)
						}))
					viaFirst := b.Have(
						"v is the combination over U₁ ∪ U₂ of a₁ extended by zero",
						"v = module_sum(M.add, M.zero, U₁ ∪ U₂, λx:B. COND(x ∈ U₁, a₁(x), R.zero) • x)",
						By(
							onFirst[3],
							finBoth,
							bothInM,
							onFirst[2],
							set_order.SubsetUnion.At(U1, U2),
							CombinationExtendByZero.Read(moduleOn).At(U1, both, a1)))
					viaSecond := b.Have(
						"and of a₂ extended by zero",
						"v = module_sum(M.add, M.zero, U₁ ∪ U₂, λx:B. COND(x ∈ U₂, a₂(x), R.zero) • x)",
						By(
							onSecond[3],
							finBoth,
							bothInM,
							onSecond[2],
							set_order.SubsetUnion.At(U2, U1),
							CombinationExtendByZero.Read(moduleOn).At(U2, both, a2)))
					same := b.Have(
						"so the two extended combinations agree",
						"module_sum(M.add, M.zero, U₁ ∪ U₂, λx:B. COND(x ∈ U₁, a₁(x), R.zero) • x) = "+
							"module_sum(M.add, M.zero, U₁ ∪ U₂, λx:B. COND(x ∈ U₂, a₂(x), R.zero) • x)",
						By(Normalized, viaFirst, viaSecond))
					agree := b.Have(
						"U₁ ∪ U₂ is a finite part of the independent S ∪ T, so the extended coefficients agree on it",
						"∀z:B. z ∈ U₁ ∪ U₂ ⇒ COND(z ∈ U₁, a₁(z), R.zero) = COND(z ∈ U₂, a₂(z), R.zero)",
						By(
							independent,
							finBoth,
							bothInUnion,
							scalars,
							same,
							IndependentUniqueCoefficients.Read(moduleOn).AsFact().At(union, both, extended1, extended2)))

					// On U₁, which U₂ does not meet, the second coefficient is zero,
					// so the first is too.
					inM := b.Unfolded(b.Have(
						"U₁ lies in M",
						"U₁ ⊆ M.carrier",
						By(onFirst[1], sInM, set_order.SubsetTrans.At(U1, S, carrier))), set_basic.SubsetDef)
					terms := b.Have(
						"so every term a₁(x) • x over U₁ vanishes",
						"∀x:B. x ∈ U₁ ⇒ a₁(x) • x = M.zero",
						Derive(func(c *Argument) {
							x := c.FixAs[B]("x")
							xIn := c.Assume()
							inBoth := c.Have(
								"x lies in U₁ ∪ U₂",
								"x ∈ U₁ ∪ U₂",
								BySets(xIn))
							outside := c.Have(
								"and outside U₂, which lies in T, which S does not meet",
								"x ∉ U₂",
								BySets(xIn, onFirst[1], onSecond[1], apart))
							zero := c.Have(
								"at x the first extended coefficient is a₁(x) and the second R.zero, so a₁(x) is R.zero",
								"a₁(x) = R.zero",
								By(agree.At(x), inBoth, xIn, outside))
							c.Show(
								"and R.zero scales x, a vector of M, to M.zero",
								zero.Rw(),
								By(xIn, inM.At(x), module.ZeroSmul.Read(moduleOn).AsFact().At(x)))
						}))
					b.Show(
						"v is the combination over U₁, all of whose terms vanish",
						By(
							Normalized,
							onFirst[3],
							onFirst[0],
							terms,
							module.ModuleSumZero.Read(moduleOn).At(U1, b.TermAs[Fun[B, B]]("λx:B. a₁(x) • x"))))
				}))
			arg.Show(
				"so the two spans meet only in M.zero",
				BySets(common))
		}),
})}

// IndependentInsertOutsideSpan — a vector that joins a set independently,
// not being in it already, lies outside the set's span; over any ring
// with one ≠ zero. {v} and S are disjoint parts of the independent
// insert(v, S), so their spans meet only in zero (IndependentSpansMeet);
// v in the span of S would lie in both and be M.zero, a member of an
// independent set, which one ≠ zero forbids (IndependentZeroNotIn).
var IndependentInsertOutsideSpan = independentInsertOutsideSpanThm{family.Add(registry.ProofEntry{
	Name: "IndependentInsertOutsideSpan",
	Key:  "prop_b06b00afae8abc8c",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B). ∀v:B.",
		Hypotheses: []string{
			"R.one ≠ R.zero",
			"module_independent(R, M, insert(v, S))",
			"v ∉ S",
		},
		Conclusion: "v ∉ module_span(R, M, S)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			S *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"R.one is not R.zero",
				"insert(v, S) is independent",
				"v lies outside S")
			oneNotZero, independent, vOutsideS := given[0], given[1], given[2]
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			single, extended := arg.TermAs[Set[B]]("{v}"), arg.TermAs[Set[B]]("insert(v, S)")
			united := arg.Have(
				"{v} ∪ S is insert(v, S)",
				"{v} ∪ S = insert(v, S)",
				BySets())
			unionIndependent := arg.Have(
				"so {v} ∪ S is independent",
				"module_independent(R, M, {v} ∪ S)",
				By(Normalized, united, independent))
			apart := arg.Have(
				"and {v} does not meet S, v lying outside it",
				"{v} ∩ S = ∅",
				BySets(vOutsideS))
			inSpan := arg.SupposeNot()
			zero := arg.Have(
				"v lies in the span of {v} too, and the two spans meet only in zero, so v is M.zero",
				"v = M.zero",
				BySets(
					inSpan,
					unionIndependent,
					apart,
					submodule.SubsetSpan.At(R, M, single),
					IndependentSpansMeet.Read(moduleOn).At(single, S)))
			arg.Show(
				"then M.zero lies in the independent insert(v, S), which R.one ≠ R.zero forbids",
				By(
					Normalized,
					zero,
					oneNotZero,
					independent,
					set_basic.InInsert.At(S, v, v),
					IndependentZeroNotIn.Read(moduleOn).At(extended)))
		}),
})}

// IndependentInsertNoMultiple — a vector of M no nonzero multiple of which
// lies in the span of an independent set joins that set independently. In
// a vanishing combination over a finite part T of insert(v, S), the term
// at v is minus the combination over the other members of T, which lie in
// S, so it lies in the span of S and its coefficient is zero; what is left
// vanishes over T ∩ S, where the independence of S clears it.
var IndependentInsertNoMultiple = independentInsertNoMultipleThm{family.Add(registry.ProofEntry{
	Name: "IndependentInsertNoMultiple",
	Key:  "prop_e87365a21b62c541",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B). ∀v:B.",
		Hypotheses: []string{
			"module_independent(R, M, S)",
			"v ∈ M.carrier",
			"∀c:A. c ∈ R.carrier ∧ c • v ∈ module_span(R, M, S) ⇒ c = R.zero",
		},
		Conclusion: "module_independent(R, M, insert(v, S))",
		Abbrev: Abbrev{
			{Name: "others", Text: "module_sum(M.add, M.zero, delete(T, v), λx:B. a(x) • x)"},
		},
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			S *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"S is independent",
				"v lies in M",
				"only R.zero scales v into the span of S")
			independent, vInM, noMultiple := given[0], given[1], given[2]
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			carrier, extended := arg.TermAs[Set[B]]("M.carrier"), arg.TermAs[Set[B]]("insert(v, S)")
			span := arg.TermAs[Set[B]]("module_span(R, M, S)")
			vM := arg.MemberOf[on.M](v, vInM)
			sInM := arg.Have(
				"S, being independent, lies in M",
				"S ⊆ M.carrier",
				By(IndependentInCarrier.Read(independent)))
			extendedInM := arg.Have(
				"insert(v, S) lies in M",
				"insert(v, S) ⊆ M.carrier",
				By(vInM, sInM, set_order.InsertSubset.At(S, carrier, v)))
			spanSubmodule := arg.Have(
				"the span of S is a submodule",
				"submodule(R, M, module_span(R, M, S))",
				By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S)))
			vanishing := arg.Have(
				"a vanishing combination over a finite part of insert(v, S) has every coefficient R.zero",
				Statement{
					Binders: "∀T:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ insert(v, S)",
						"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
						"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero",
					},
					Conclusion: "∀x:B. x ∈ T ⇒ a(x) = R.zero",
				},
				Derive(func(c *Argument) {
					T := c.FixAs[Set[B]]("T")
					a := c.FixAs[Fun[B, A]]("a")
					about := c.Conjuncts(
						c.Assume(),
						"T is finite",
						"T lies in insert(v, S)",
						"a is a scalar on T",
						"the combination of a over T vanishes")
					finT, tInExtended, coefficients, vanishes := about[0], about[1], about[2], about[3]
					tInM := c.Have(
						"T lies in M",
						"T ⊆ M.carrier",
						By(tInExtended, extendedInM, set_order.SubsetTrans.At(T, extended, carrier)))
					inM := c.Unfolded(tInM, set_basic.SubsetDef)
					combination := c.TermAs[Fun[B, B]]("λx:B. a(x) • x")
					terms := c.Have(
						"each term a(x) • x over T lies in M",
						"∀x:B. x ∈ T ⇒ a(x) • x ∈ M.carrier",
						c.ForEach(func(x *Expr[B]) Action {
							return By(inM.At(x), coefficients.At(x), module.SmulIn.Read(moduleOn))
						}))
					atV := c.Have(
						"if v is in T, a(v) • v is minus the combination over the "+
							"other members, a vector of the span of S, so a(v) is zero",
						"v ∈ T ⇒ a(v) = R.zero",
						Derive(func(d *Argument) {
							vInT := d.Assume()
							rest := d.TermAs[Set[B]]("delete(T, v)")
							split := d.Have(
								"the combination is a(v) • v plus the combination over the other members",
								"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = a(v) • v + «others»",
								By(finT, vInT, terms, module.ModuleSumDelete.Read(moduleOn).At(T, v, combination)))
							othersInSpan := d.Have(
								"the members of T but v lie in S, so in its span",
								"∀x:B. x ∈ T ∧ x ≠ v ⇒ x ∈ module_span(R, M, S)",
								BySets(tInExtended, submodule.SubsetSpan.At(R, M, S)))
							restTerms := d.Have(
								"so each term over the other members lies in the span of S, a submodule",
								"∀x:B. x ∈ delete(T, v) ⇒ a(x) • x ∈ module_span(R, M, S)",
								Derive(func(e *Argument) {
									x := e.FixAs[B]("x")
									e.Show(
										"x lies in the span of S and a(x) is a scalar",
										By(
											e.Assume(),
											set_basic.InDelete.At(T, x, v),
											othersInSpan.At(x),
											coefficients.At(x),
											submodule.SubmoduleSmul.Read(spanSubmodule).AsFact().At(e.TermAs[A]("a(x)"), x)))
								}))
							othersIn := d.Have(
								"and their combination, a finite sum of vectors of the span of S, lies in it",
								"«others» ∈ module_span(R, M, S)",
								By(
									spanSubmodule,
									finT,
									finite_set.FiniteDeleteImp.At(T, v),
									restTerms,
									submodule.SubmoduleModuleSum.Read(moduleOn).At(span, rest, combination)))
							coefIn := d.Have(
								"a(v) is a scalar",
								"a(v) ∈ R.carrier",
								By(coefficients.At(v), vInT))
							coef := d.MemberOf[on.R](d.TermAs[A]("a(v)"), coefIn)
							othersInM := d.Have(
								"the combination over the other members lies in M",
								"«others» ∈ M.carrier",
								BySets(othersIn, submodule.SubmoduleSubset.Read(spanSubmodule)))
							othersM := d.MemberOf[on.M](d.TermAs[B]("«others»"), othersInM)
							difference := d.Have(
								"a(v) • v is the combination less the others",
								"a(v) • v = module_sum(M.add, M.zero, T, λx:B. a(x) • x) + -«others»",
								By(
									split,
									group.MulInvCancelRightOn.Read(module.AddGroupOn.Read(moduleOn)).At(
										othersM, module.SmulIn.Read(moduleOn).At(coef, vM))))
							sumInSpan := d.Have(
								"the combination, M.zero, lies in the span of S",
								"module_sum(M.add, M.zero, T, λx:B. a(x) • x) ∈ module_span(R, M, S)",
								By(vanishes, submodule.SubmoduleZero.Read(spanSubmodule)))
							termIn := d.Have(
								"so a(v) • v, the difference of two vectors of the span of S, lies in it",
								"a(v) • v ∈ module_span(R, M, S)",
								By(
									difference,
									sumInSpan,
									othersIn,
									submodule.SubmoduleSub.Read(spanSubmodule).AsFact().At(
										d.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. a(x) • x)"), d.TermAs[B]("«others»"))))
							d.Show(
								"and only R.zero scales v into the span of S",
								By(coefIn, termIn, noMultiple.At(d.TermAs[A]("a(v)"))))
						}))
					common := c.TermAs[Set[B]]("T ∩ S")
					offS := c.Have(
						"a member of T outside S is v, whose term R.zero • v vanishes",
						"∀x:B. x ∈ T ∧ x ∉ T ∩ S ⇒ a(x) • x = M.zero",
						BySets(tInExtended, atV, module.ZeroSmul.Read(moduleOn).At(vM)))
					onCommon := c.Have(
						"so the combination over T is the one over T ∩ S, which vanishes",
						"module_sum(M.add, M.zero, T ∩ S, λx:B. a(x) • x) = M.zero",
						By(
							vanishes,
							finT,
							terms,
							offS,
							set_order.InterSubset.At(T, S),
							module.ModuleSumSupport.Read(moduleOn).At(T, common, combination)))
					commonInS := c.Have(
						"T ∩ S lies in S",
						"T ∩ S ⊆ S",
						BySets())
					commonCoefficients := c.Have(
						"and a is a scalar on it",
						"∀x:B. x ∈ T ∩ S ⇒ a(x) ∈ R.carrier",
						BySets(coefficients))
					cleared := c.Have(
						"the independence of S clears a on T ∩ S",
						"∀x:B. x ∈ T ∩ S ⇒ a(x) = R.zero",
						By(
							Normalized,
							finT,
							finite_set.FiniteInter.At(T, S),
							commonInS,
							commonCoefficients,
							onCommon,
							IndependentVanishingCombination.Read(independent).AsFact().At(common, a)))
					c.Show(
						"so a vanishes on T: on T ∩ S, and at v, its one member outside S",
						c.ForEach(func(x *Expr[B]) Action {
							return BySets(tInExtended, cleared.At(x), atV)
						}))
				}))
			arg.Show(
				"so insert(v, S) is independent",
				By(extendedInM, vanishing, ModuleIndependentDef.At(R, M, extended)))
		}),
})}

// IndependentPartSpansMultiple — over an integral domain, a finite set G of
// vectors has an independent part S and a nonzero scalar a with a • g in
// the span of S for every g of G. By induction on G: at ∅ the empty part
// and R.one serve. At a new vector x, when some nonzero d puts d • x in the
// span of S, the part S stays and d * a, nonzero in a domain, serves;
// otherwise x joins S independently (IndependentInsertNoMultiple), and a
// still serves, the span of S lying in the span of insert(x, S).
var IndependentPartSpansMultiple = independentPartSpansMultipleThm{family.Add(registry.ProofEntry{
	Name: "IndependentPartSpansMultiple",
	Key:  "prop_355e7511419b2c18",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀G:set(B).",
		Hypotheses: []string{
			"integral_domain_on(R)",
			"finite(G)",
			"G ⊆ M.carrier",
		},
		Conclusion: "∃S:set(B). ∃a:A. " +
			"    S ⊆ G ∧ " +
			"    module_independent(R, M, S) ∧ " +
			"    a ∈ R.carrier ∧ " +
			"    a ≠ R.zero ∧ " +
			"    (∀g:B. g ∈ G ⇒ a • g ∈ module_span(R, M, S))",
	},
		func(arg *Argument, moduleOn module.ModuleFact[on.R, on.M], G *Expr[Set[B]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"R is an integral domain",
				"G is finite",
				"G lies in M")
			domain, finG, gInM := given[0], given[1], given[2]
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			ring := module.RingOn.Read(moduleOn)
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			carrier := arg.TermAs[Set[B]]("M.carrier")
			pointwise := arg.Unfolded(gInM, set_basic.SubsetDef)
			arg.Show(
				"the induction carries the part and the scalar to every finite set of vectors of M, G among them",
				ByInduction(finite_set.FiniteInductFreshOn, finG, pointwise,
					Case(
						"at ∅: the empty part, independent, and the scalar R.one, not zero in a domain",
						Derive(func(b *Argument) {
							empty := b.TermAs[Set[B]]("∅")
							b.Take(empty)
							b.Take(b.TermAs[A]("R.one"))
							b.Show(
								"∅ lies in ∅ and is independent, R.one is a nonzero scalar, and ∅ holds no vector to scale",
								By(
									set_order.EmptySubset.At(empty),
									IndependentEmpty.At(R, M),
									comm_ring.OneIn.Read(ring),
									integral_domain.OneNotZero.Read(domain),
									set_basic.NotInEmpty))
						})),
					Case(
						"at a new vector x of M: S stays when a nonzero "+
							"multiple of x lies in its span, and x joins S otherwise",
						Derive(func(b *Argument) {
							x := b.FixAs[B]("x")
							b.FixAs[Set[B]]("T")
							carried := b.Conjuncts(
								b.Assume(),
								"T has an independent part S and a scalar a",
								"x is new to T",
								"T is finite",
								"x lies in M",
								"T lies in M")
							S, a, atT := b.Unpack2As[Set[B], A](carried[0], "S", "a")
							ofS := b.Conjuncts(
								atT,
								"S lies in T",
								"S is independent",
								"a is a scalar",
								"a is not zero",
								"a • g lies in the span of S for every g of T")
							sInT, independent, aIn, aNonzero, multiples := ofS[0], ofS[1], ofS[2], ofS[3], ofS[4]
							xM, aR := b.MemberOf[on.M](x, carried[3]), b.MemberOf[on.R](a, aIn)
							sInM := b.Have(
								"S lies in M",
								"S ⊆ M.carrier",
								By(IndependentInCarrier.Read(independent)))
							spanSub := b.Have(
								"the span of S is a submodule of M",
								"submodule(R, M, module_span(R, M, S))",
								By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S)))
							b.Cases(b.Term("∃d:A. d ∈ R.carrier ∧ d ≠ R.zero ∧ d • x ∈ module_span(R, M, S)"))
							b.When(
								"a nonzero multiple d • x lies in the span of S: S stays, "+
									"and d * a scales every vector of insert(x, T) into its span",
								func(c *Argument, some Fact) {
									d, dIs := c.UnpackAs[A](some, "d")
									ofD := c.Conjuncts(
										dIs,
										"d is a scalar",
										"d is not zero",
										"d • x lies in the span of S")
									dIn, dNonzero, dxIn := ofD[0], ofD[1], ofD[2]
									dR := c.MemberOf[on.R](d, dIn)
									product := c.TermAs[A]("d * a")
									// The domain fact is the plain hypothesis, a reading at no carrier
									// phantom: its law takes d and a paired with their memberships by hand.
									productNonzero := c.Have(
										"d * a is not zero, R having no zero divisors",
										"d * a ≠ R.zero",
										By(
											dNonzero,
											aNonzero,
											integral_domain.NoZeroDivisors.Read(domain).At(proof.MemberOf(d, dIn), proof.MemberOf(a, aIn))))
									regroup := c.Have(
										"scaling x by d * a is scaling d • x by a",
										"(d * a) • x = a • (d • x)",
										CalcEq(
											Leg(
												c.TermAs[B]("(a * d) • x"),
												"the scalars commute",
												By(Normalized, comm_monoid.CommOn.Read(mulMonoid).At(dR, aR))),
											FinalLeg(
												"and scaling by a product is scaling twice",
												By(module.SmulMul.Read(moduleOn).At(aR, dR, xM))),
										))
									atX := c.Have(
										"so (d * a) • x, a multiple of d • x, lies in the span of S",
										"(d * a) • x ∈ module_span(R, M, S)",
										regroup.Rw(),
										By(submodule.SubmoduleSmul.Read(spanSub).At(
											proof.MemberOf(a, aIn), proof.MemberOf(c.TermAs[B]("d • x"), dxIn))))
									onT := c.Have(
										"and (d * a) • g is d • (a • g), a multiple of a vector of the span of S, for every g of T",
										"∀g:B. g ∈ T ⇒ (d * a) • g ∈ module_span(R, M, S)",
										Derive(func(e *Argument) {
											g := e.FixAs[B]("g")
											gInT := e.Assume()
											gM := e.MemberOf[on.M](g, GroupPremises(gInT, carried[4].At(g)))
											e.Show(
												"scaling by d * a is scaling by a and then by d",
												By(
													Normalized,
													module.SmulMul.Read(moduleOn).At(dR, aR, gM),
													multiples.At(g),
													gInT,
													dIn,
													submodule.SubmoduleSmul.Read(spanSub).AsFact().At(d, e.TermAs[B]("a • g"))))
										}))
									everywhere := c.Have(
										"so d * a scales every vector of insert(x, T) into the span of S",
										"∀g:B. g ∈ insert(x, T) ⇒ d * a • g ∈ module_span(R, M, S)",
										BySets(atX, onT))
									sInExtended := c.Have(
										"S lies in T, inside insert(x, T)",
										"S ⊆ insert(x, T)",
										BySets(sInT))
									c.Take(S)
									c.Take(product)
									c.Show(
										"S and d * a serve insert(x, T)",
										By(sInExtended, independent, comm_ring.MulIn.Read(ring).At(dR, aR), productNonzero, everywhere))
								})
							b.Otherwise(
								"no nonzero multiple of x lies in the span of S: x joins S "+
									"independently, and a scales every vector of insert(x, T) into its span",
								func(c *Argument, none Fact) {
									noMultiple := c.Have(
										"only R.zero scales x into the span of S",
										"∀d:A. d ∈ R.carrier ∧ d • x ∈ module_span(R, M, S) ⇒ d = R.zero",
										By(none))
									grown := c.TermAs[Set[B]]("insert(x, S)")
									joins := c.Have(
										"so insert(x, S) is independent",
										"module_independent(R, M, insert(x, S))",
										By(independent, noMultiple, IndependentInsertNoMultiple.Read(moduleOn).At(S, xM)))
									grownInM := c.Have(
										"insert(x, S) lies in M",
										"insert(x, S) ⊆ M.carrier",
										By(xM, sInM, set_order.InsertSubset.At(S, carrier, x)))
									grownSpan := c.Have(
										"its span is a submodule of M",
										"submodule(R, M, module_span(R, M, insert(x, S)))",
										By(grownInM, submodule.SpanSubmodule.Read(moduleOn).At(grown)))
									xIn := c.Have(
										"x lies in insert(x, S), inside its span",
										"x ∈ module_span(R, M, insert(x, S))",
										BySets(submodule.SubsetSpan.At(R, M, grown)))
									everywhere := c.Have(
										"so a • x lies in that span, and a • g does for each g of T, the span of S lying inside it",
										"∀g:B. g ∈ insert(x, T) ⇒ a • g ∈ module_span(R, M, insert(x, S))",
										BySets(
											submodule.SubmoduleSmul.Read(grownSpan).At(proof.MemberOf(a, aIn), proof.MemberOf(x, xIn)),
											multiples,
											submodule.SpanMono.At(R, M, S, grown)))
									grownInExtended := c.Have(
										"insert(x, S) lies in insert(x, T)",
										"insert(x, S) ⊆ insert(x, T)",
										BySets(sInT))
									c.Take(grown)
									c.Take(a)
									c.Show(
										"insert(x, S) and a serve insert(x, T)",
										By(grownInExtended, joins, aIn, aNonzero, everywhere))
								})
						})),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Under a homomorphism, over any ring
// ---------------------------------------------------------------------------

// HomSpan — a homomorphism carries the span of a subset of M onto the
// span of the subset's image: f sends a combination of S to the
// combination of the images with the same coefficients, a vector of the
// span of the images; and f carries the submodule span(S) to a submodule
// of N holding the images of S, so holding their span.
var HomSpan = homSpanThm{family.Add(registry.ProofEntry{
	Name: "HomSpan",
	Key:  "prop_3536d2f4746948a8",
	Reading: "S ⊆ M.carrier is load-bearing: for S ⊄ M.carrier no submodule of M holds " +
		"S, so its span is ⋂∅ = 𝕌, whose image under f need not be the span of image(f, S).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"S ⊆ M.carrier",
		},
		Conclusion: "image(f, module_span(R, M, S)) = module_span(R, N, image(f, S))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"f is a homomorphism",
				"S lies in M")
			linear, sInM := given[0], given[1]
			moduleM, moduleN :=
				module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
			span, images := a.TermAs[Set[B]]("module_span(R, M, S)"), a.TermAs[Set[C]]("image(f, S)")
			spanImages, imageOfSpan :=
				a.TermAs[Set[C]]("module_span(R, N, image(f, S))"),
				a.TermAs[Set[C]]("image(f, module_span(R, M, S))")
			inM := a.Unfolded(sInM, set_basic.SubsetDef)
			imagesInN := a.Have(
				"the images of S lie in N",
				"image(f, S) ⊆ N.carrier",
				Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
				By(inM, module_homomorphism.HomIn.Read(linear)))
			spanSub := a.Have(
				"the span of S is a submodule of M",
				"submodule(R, M, module_span(R, M, S))",
				By(sInM, submodule.SpanSubmodule.Read(moduleM).At(S)))
			spanImagesSub := a.Have(
				"and the span of the images a submodule of N",
				"submodule(R, N, module_span(R, N, image(f, S)))",
				By(imagesInN, submodule.SpanSubmodule.Read(moduleN).At(images)))

			// ⊆: f sends a combination of S to the combination of the images
			// with the same coefficients, a finite sum of vectors of the span of
			// the images, which holds f(z) for every z of S.
			inSpan := a.Simplified(
				submodule.SubsetSpan.At(R, N, images),
				Fwd(set_basic.SubsetDef),
				Fwd(set_image.ForallInImage))
			reached := a.Have(
				"f carries the span of S into the span of the images",
				"∀x:B. x ∈ module_span(R, M, S) ⇒ f(x) ∈ module_span(R, N, image(f, S))",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					T, _, xIs := b.Obtain2As[Set[B], Fun[B, A]](
						"x is a combination of S over a finite T",
						"∃T:set(B). ∃c:(B → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ S ∧ "+
							"    (∀z:B. z ∈ T ⇒ c(z) ∈ R.carrier) ∧ "+
							"    x = module_sum(M.add, M.zero, T, λz:B. c(z) • z)",
						By(xIn, sInM, SpanMembership.Read(moduleM).At(S, x)))
					about := b.Conjuncts(
						xIs,
						"T is finite",
						"T lies in S",
						"c is a scalar on T",
						"x is the combination of c over T")
					inS := b.Unfolded(about[1], set_basic.SubsetDef)
					tInM := b.Unfolded(b.Have(
						"T lies in M",
						"T ⊆ M.carrier",
						By(
							about[1],
							sInM,
							set_order.SubsetTrans.At(T, S, b.TermAs[Set[B]]("M.carrier")))), set_basic.SubsetDef)
					terms := b.Have(
						"each term c(z) • z lies in M, and f sends it to c(z) • f(z)",
						"∀z:B. z ∈ T ⇒ c(z) • z ∈ M.carrier ∧ f(c(z) • z) = c(z) • f(z)",
						b.ForEach(func(z *Expr[B]) Action {
							return By(
								tInM.At(z),
								about[2].At(z),
								module.SmulIn.Read(moduleM),
								module_homomorphism.HomSmul.Read(linear))
						}))
					multiples := b.Have(
						"each c(z) • f(z) lies in the span of the images, a submodule holding f(z)",
						"∀z:B. z ∈ T ⇒ c(z) • f(z) ∈ module_span(R, N, image(f, S))",
						b.ForEach(func(z *Expr[B]) Action {
							return By(inS.At(z), inSpan.At(z), about[2].At(z), submodule.SubmoduleSmul.Read(spanImagesSub))
						}))
					combination := b.TermAs[Fun[B, C]]("λz:B. c(z) • f(z)")
					value := b.Have(
						"f(x) is the combination of the images with the same coefficients",
						"f(x) = module_sum(N.add, N.zero, T, λz:B. c(z) • f(z))",
						By(
							about[3],
							about[0],
							terms,
							module_homomorphism.HomSum.Read(linear).At(T, b.TermAs[Fun[B, B]]("λz:B. c(z) • z")),
							module.ModuleSumCongruence.At(
								b.TermAs[Op[C]]("N.add"),
								b.TermAs[C]("N.zero"),
								T,
								b.TermAs[Fun[B, C]]("λz:B. f(c(z) • z)"),
								combination)))
					b.Show(
						"a submodule holds every finite sum of its vectors, the span of the images among them",
						By(
							value,
							about[0],
							multiples,
							spanImagesSub,
							submodule.SubmoduleModuleSum.Read(moduleN).At(spanImages, T, combination)))
				}))
			forward := a.Have(
				"so the image of the span lies in the span of the images",
				"image(f, module_span(R, M, S)) ⊆ module_span(R, N, image(f, S))",
				Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
				By(reached))

			// ⊇: f restricted to the submodule span(S) is a homomorphism, whose
			// image is a submodule of N holding the images of S.
			whole := a.Have(
				"N restricted to its own carrier is N",
				"restrict_module(N, N.carrier) = N",
				Simp(Fwd(module_record.RestrictModuleDef)),
				By(module_record.ModuleOpsData.Ext))
			into := a.Have(
				"f maps the span of S into N",
				"∀u:B. u ∈ module_span(R, M, S) ⇒ f(u) ∈ N.carrier",
				BySets(submodule.SubmoduleSubset.Read(spanSub), module_homomorphism.HomIn.Read(linear)))
			restricted := a.Have(
				"f restricted to the span of S is a homomorphism into N",
				"module_homomorphism(R, restrict_module(M, module_span(R, M, S)), N, f)",
				By(
					Normalized,
					whole,
					linear,
					spanSub,
					into,
					submodule.CarrierSubmodule.Read(moduleN),
					module_homomorphism.HomRestrict.At(R, M, N, f, span, a.TermAs[Set[C]]("N.carrier"))))
			backward := a.Have(
				"the image of the span, a submodule of N, holds the images of S ⊆ span(S), so it holds their span",
				"module_span(R, N, image(f, S)) ⊆ image(f, module_span(R, M, S))",
				By(
					restricted,
					module_homomorphism.ImageSubmodule.At(
						R, a.TermAs[ModuleOps[A, B]]("restrict_module(M, module_span(R, M, S))"), N, f),
					set_image.ImageSubset.At(f, S, span),
					submodule.SubsetSpan.At(R, M, S),
					submodule.SpanLeast.At(R, N, images, imageOfSpan)))
			a.Show(
				"each lies in the other",
				By(forward, backward, set_order.SubsetAntisym.At(imageOfSpan, spanImages)))
		}),
})}

// HomSpanInSubmodule — a homomorphism sends the span of a subset S of M
// into every submodule of N holding the image of S: the image of the span
// is the span of the image, the least submodule holding it.
var HomSpanInSubmodule = homSpanInSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "HomSpanInSubmodule",
	Key:  "prop_240914a436659330",
	Reading: "S ⊆ M.carrier is load-bearing: for S ⊄ M.carrier no submodule of " +
		"M holds S, so its span is ⋂∅ = 𝕌, whose image under f need not lie in P.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀S:set(B). " +
			"∀P:set(C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"S ⊆ M.carrier",
			"submodule(R, N, P)",
			"image(f, S) ⊆ P",
		},
		Conclusion: "image(f, module_span(R, M, S)) ⊆ P",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			P *Expr[Set[C]],
			linear, inM, subP, imageInP Fact,
		) {
			a.Show(
				"the image of the span is the span of the image, which lies in the submodule P holding the image",
				By(
					Normalized,
					linear,
					inM,
					subP,
					imageInP,
					HomSpan.At(R, M, N, f, S),
					submodule.SpanLeast.At(R, N, a.TermAs[Set[C]]("image(f, S)"), P)))
		}),
})}

// HomAgreeOnSpan — two homomorphisms agreeing on a subset S of M agree on
// its span: the kernel of their difference is a submodule of M holding S, so
// it holds the span of S, and where the difference vanishes the two values
// are one.
var HomAgreeOnSpan = homAgreeOnSpanThm{family.Add(registry.ProofEntry{
	Name: "HomAgreeOnSpan",
	Key:  "prop_818527e085ef37cf",
	Reading: "S ⊆ M.carrier is load-bearing: for S ⊄ M.carrier no submodule " +
		"of M holds S, so its span is ⋂∅ = 𝕌, on which f and g need not agree.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀f g:(B → C). " +
			"∀S:set(B). " +
			"∀y:B.",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"module_homomorphism(R, M, N, g)",
			"S ⊆ M.carrier",
			"∀x:B. x ∈ S ⇒ f(x) = g(x)",
			"y ∈ module_span(R, M, S)",
		},
		Conclusion: "f(y) = g(y)",
		Abbrev: Abbrev{
			{Name: "difference", Text: "λu:B. N.add(f(u), N.neg(g(u)))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f, g *Arrow[B, C],
			S *Expr[Set[B]],
			y *Expr[B],
			fLinear, gLinear, inM, agree, inSpan Fact,
		) {
			target := module_homomorphism.HomTarget.Read(fLinear)
			zero := a.TermAs[C]("N.zero")
			carrier := a.TermAs[Set[B]]("M.carrier")
			difference := a.TermAs[Fun[B, C]]("«difference»")
			linear := a.Have(
				"the difference of the two maps is linear",
				"module_homomorphism(R, M, N, «difference»)",
				By(fLinear, gLinear, module_homomorphism.HomDiff.At(R, M, N, f, g)))
			within := a.Unfolded(inM, set_basic.SubsetDef)
			holdsS := a.Have(
				"its kernel holds S, where f and g agree",
				"S ⊆ group_kernel(N.zero, M.carrier, «difference»)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inS := b.Assume()
					xm := proof.MemberOf(x, b.Have(
						"x lies in M",
						"x ∈ M.carrier",
						By(within.At(x), inS)))
					b.Show(
						"the difference at x is g(x) + -g(x), which is N.zero",
						By(
							Normalized,
							agree.At(x),
							inS,
							xm,
							module_homomorphism.HomIn.Read(gLinear).At(xm),
							group_homomorphism.InKernel.At(zero, carrier, difference, x),
							group.RightInverseOn.Read(module.AddGroupOn.Read(target)).AsFact().At(g.Apply(x))))
				}))
			holdsSpan := a.Have(
				"the kernel, a submodule of M holding S, holds the span of S",
				"module_span(R, M, S) ⊆ group_kernel(N.zero, M.carrier, «difference»)",
				By(
					holdsS,
					module_homomorphism.KernelSubmodule.Read(linear),
					submodule.SpanLeast.At(R, M, S, a.TermAs[Set[B]]("group_kernel(N.zero, M.carrier, «difference»)"))))
			point := a.Conjuncts(
				a.Have(
					"y is a vector of M where the difference vanishes",
					"y ∈ M.carrier ∧ f(y) + -g(y) = N.zero",
					BySets(inSpan, holdsSpan, group_homomorphism.InKernel.At(zero, carrier, difference, y))),
				"y lies in M",
				"the difference vanishes at y")
			a.Show(
				"cancelling the zero difference in N, the two values are one",
				ByChase(Depth(0), target, fLinear, gLinear, point[0], point[1]))
		}),
})}

// SpanInsertKernel — a linear functional φ on M that is R.one at e and
// R.zero on S cuts the span of insert(e, S) down to the span of S: a
// vector c • e + w of the larger span, w in the span of S, has φ-value
// c, since the span of S is a submodule inside the kernel of φ; so φ
// kills it only at c = R.zero, where it is w.
var SpanInsertKernel = spanInsertKernelThm{family.Add(registry.ProofEntry{
	Name: "SpanInsertKernel",
	Key:  "prop_117176dde5186873",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B). ∀e:B. ∀φ:(B → A). ∀v:B.",
		Hypotheses: []string{
			"S ⊆ M.carrier",
			"e ∈ M.carrier",
			"module_homomorphism(R, M, regular_module(R), φ)",
			"φ(e) = R.one",
			"∀x:B. x ∈ S ⇒ φ(x) = R.zero",
			"v ∈ module_span(R, M, insert(e, S)) ∧ φ(v) = R.zero",
		},
		Conclusion: "v ∈ module_span(R, M, S)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			S *Expr[Set[B]],
			e *Expr[B],
			φ *Arrow[B, A],
			hypotheses Fact,
			v *Expr[B],
			given Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"S lies in M",
				"e lies in M",
				"φ is linear",
				"φ(e) is R.one",
				"φ kills S")
			sInM, eInM, linear, atE, killsS := parts[0], parts[1], parts[2], parts[3], parts[4]
			about := arg.Conjuncts(
				given,
				"v lies in the span of insert(e, S)",
				"φ kills v")
			vIn, killsV := about[0], about[1]
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			regular := arg.TermAs[ModuleOps[A, A]]("regular_module(R)")
			ring, additive := module.RingOn.Read(moduleOn), module.AddGroupOn.Read(moduleOn)
			em := arg.MemberOf[on.M](e, eInM)

			sInKernel := arg.Have(
				"S lies in M and φ kills it, so S lies in the kernel",
				"S ⊆ group_kernel(R.zero, M.carrier, φ)",
				BySets(sInM, killsS, group_homomorphism.InKernel))
			spanInKernel := arg.Have(
				"so does the span of S, the least submodule holding S",
				"module_span(R, M, S) ⊆ group_kernel(R.zero, M.carrier, φ)",
				By(
					linear,
					module_homomorphism.KernelSubmodule.At(R, M, regular, φ),
					sInKernel,
					submodule.SpanLeast.At(R, M, S, arg.TermAs[Set[B]]("group_kernel(R.zero, M.carrier, φ)"))))
			c, w, written := arg.Obtain2As[A, B](
				"v is c • e + w for a scalar c and a w in the span of S",
				"∃c:A. ∃w:B. c ∈ R.carrier ∧ w ∈ module_span(R, M, S) ∧ v = c • e + w",
				BySets(vIn, sInM, submodule.SpanInsert.Read(moduleOn).At(S, em)))
			terms := arg.Conjuncts(
				written,
				"c is a scalar",
				"w lies in the span of S",
				"v is c • e + w")
			cIn, vIs := terms[0], terms[2]
			wKernel := arg.Conjuncts(
				arg.Simplified(
					GroupPremises(terms[1], arg.Unfolded(spanInKernel, set_basic.SubsetDef).At(w)),
					Fwd(group_homomorphism.InKernel)),
				"w lies in M",
				"φ kills w")
			cm, wm := arg.MemberOf[on.R](c, cIn), arg.MemberOf[on.M](w, wKernel[0])
			multiple := module.SmulIn.Read(moduleOn).At(cm, em)

			value := arg.Have(
				"φ(v) = c·φ(e) + φ(w) = c",
				"φ(v) = c",
				CalcEq(
					Leg(
						arg.TermAs[A]("φ(c • e + w)"),
						"v is c • e + w",
						By(Normalized, vIs)),
					Leg(
						arg.TermAs[A]("φ(c • e) + φ(w)"),
						"φ is additive",
						By(module_homomorphism.HomAdd.Read(linear).AsFact().At(arg.TermAs[B]("c • e"), w), multiple, wm)),
					Leg(
						arg.TermAs[A]("c * R.one + R.zero"),
						"φ(c • e) is c·φ(e) = c·R.one, and φ kills w",
						GroupPremises(terms[0], parts[1], module_homomorphism.HomSmul.Read(linear).AsFact().At(c, e)).Rw(),
						atE.Rw(),
						wKernel[1].Rw(),
						Basic()),
					FinalLeg(
						"which is c in the ring R",
						ByArith(ring, cIn)),
				))
			zero := arg.Have(
				"φ kills v, so c is R.zero",
				"c = R.zero",
				By(Normalized, value, killsV))
			isW := arg.Have(
				"so v is w",
				"v = w",
				CalcEq(
					Leg(
						arg.TermAs[B]("c • e + w"),
						"v is c • e + w",
						By(vIs)),
					Leg(
						arg.TermAs[B]("R.zero • e + w"),
						"c is R.zero",
						zero.Rw(),
						Basic()),
					Leg(
						arg.TermAs[B]("M.zero + w"),
						"R.zero • e is M.zero",
						By(Normalized, module.ZeroSmul.Read(moduleOn).At(em))),
					FinalLeg(
						"M.zero is the additive identity",
						By(group.LeftIdentityOn.Read(additive).At(wm))),
				))
			arg.Show(
				"and w lies in the span of S",
				isW.Rw(),
				Assumption())
		}),
})}

// IndependentImage — a one-to-one homomorphism carries an independent set
// to an independent set: a vanishing combination of images is f of the
// combination of their preimages with the same coefficients, which f
// sends to N.zero = f(M.zero), so it is M.zero, and S's independence
// clears every coefficient.
var IndependentImage = independentImageThm{family.Add(registry.ProofEntry{
	Name: "IndependentImage",
	Key:  "prop_fdd2fafa90b5448d",
	Reading: "f one-to-one on all of M.carrier, not only on S, is load-bearing: (x, y) ↦ x + 2y is " +
		"one-to-one on the independent {(1, 0), (0, 1)} of ℝ² and sends it to the dependent {1, 2} of ℝ.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"injective_on(M.carrier, f)",
			"module_independent(R, M, S)",
		},
		Conclusion: "module_independent(R, N, image(f, S))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"f is a homomorphism",
				"f is one-to-one on M",
				"S is independent")
			linear, injective, independent := given[0], given[1], given[2]
			moduleM, moduleN :=
				module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
			sInM := a.Have(
				"S, being independent, lies in M",
				"S ⊆ M.carrier",
				By(IndependentInCarrier.Read(independent)))
			carrierM, images := a.TermAs[Set[B]]("M.carrier"), a.TermAs[Set[C]]("image(f, S)")
			imagesInN := a.Have(
				"the images of S lie in N",
				"image(f, S) ⊆ N.carrier",
				Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
				By(a.Unfolded(sInM, set_basic.SubsetDef), module_homomorphism.HomIn.Read(linear)))
			oneToOne := a.Unfolded(injective, functions.InjectiveOnDef)

			// A vanishing combination of images over T is f of the combination
			// u of their preimages U with the same coefficients: f(u) = N.zero =
			// f(M.zero), so u = M.zero, and S's independence clears them.
			vanishing := a.Have(
				"a combination of the images of S that vanishes has every coefficient zero",
				Statement{
					Binders: "∀T:set(C). ∀c:(C → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ image(f, S)",
						"∀y:C. y ∈ T ⇒ c(y) ∈ R.carrier",
						"module_sum(N.add, N.zero, T, λy:C. c(y) • y) = N.zero",
					},
					Conclusion: "∀y:C. y ∈ T ⇒ c(y) = R.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[C]]("T")
					b.FixAs[Fun[C, A]]("c")
					given := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T lies among the images",
						"c is a scalar on T",
						"the combination vanishes")
					U, preimage := b.ObtainAs[Set[B]](
						"T is the image of a part U of S on which f is one-to-one",
						"∃U:set(B). U ⊆ S ∧ T = image(f, U) ∧ injective_on(U, f)",
						By(given[1], set_image.SubsetImageInj.At(f, T, S)))
					onU := b.Conjuncts(
						preimage,
						"U lies in S",
						"T is the image of U",
						"f is one-to-one on U")
					finiteU := b.Have(
						"U is finite, f being one-to-one on it with the finite image T",
						"finite(U)",
						By(Normalized, onU[1], onU[2], given[0], finite_set.FiniteImageInjEq.At(f, U)))
					inM := b.Unfolded(b.Have(
						"U lies in M",
						"U ⊆ M.carrier",
						By(onU[0], sInM, set_order.SubsetTrans.At(U, S, carrierM))), set_basic.SubsetDef)
					intoT := b.Have(
						"f carries U into its image T",
						"∀x:B. x ∈ U ⇒ f(x) ∈ T",
						b.ForEach(func(x *Expr[B]) Action {
							return By(Normalized, onU[1], set_image.FunInImage.At(f, U, x))
						}))
					scalarsU := b.Have(
						"so c(f(x)) is a scalar on U",
						"∀x:B. x ∈ U ⇒ c(f(x)) ∈ R.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(intoT.At(x), given[2].At(f.Apply(x)))
						}))
					termsN := b.Have(
						"each c(f(x)) • f(x) lies in N",
						"∀x:B. x ∈ U ⇒ c(f(x)) • f(x) ∈ N.carrier",
						b.ForEach(func(x *Expr[B]) Action {
							return By(
								inM.At(x),
								scalarsU.At(x),
								module.SmulIn.Read(moduleN),
								module_homomorphism.HomIn.Read(linear))
						}))
					termsM := b.Have(
						"each c(f(x)) • x lies in M, and f sends it to c(f(x)) • f(x)",
						"∀x:B. x ∈ U ⇒ c(f(x)) • x ∈ M.carrier ∧ f(c(f(x)) • x) = c(f(x)) • f(x)",
						b.ForEach(func(x *Expr[B]) Action {
							return By(
								inM.At(x),
								scalarsU.At(x),
								module.SmulIn.Read(moduleM),
								module_homomorphism.HomSmul.Read(linear))
						}))
					u := b.TermAs[B]("module_sum(M.add, M.zero, U, λx:B. c(f(x)) • x)")
					combination := b.TermAs[Fun[B, B]]("λx:B. c(f(x)) • x")
					pullback := b.Have(
						"the vanishing combination is f of the combination u of U with the coefficients c(f(x))",
						"module_sum(N.add, N.zero, T, λy:C. c(y) • y) = f(module_sum(M.add, M.zero, U, λx:B. c(f(x)) • x))",
						CalcEq(
							Leg(
								b.TermAs[C]("module_sum(N.add, N.zero, U, λx:B. c(f(x)) • f(x))"),
								"T is the one-to-one image of U",
								By(
									onU[1],
									finiteU,
									onU[2],
									termsN,
									module.ModuleSumImage.Read(moduleN).At(U, f, b.TermAs[Fun[C, C]]("λy:C. c(y) • y")))),
							FinalLeg(
								"and f carries u to that combination, term by term",
								By(
									finiteU,
									termsM,
									module_homomorphism.HomSum.Read(linear).At(U, combination),
									module.ModuleSumCongruence.At(b.TermAs[Op[C]]("N.add"), b.TermAs[C]("N.zero"), U,
										b.TermAs[Fun[B, C]]("λx:B. f(c(f(x)) • x)"), b.TermAs[Fun[B, C]]("λx:B. c(f(x)) • f(x)")))),
						))
					uIn := b.Have(
						"u lies in M",
						"module_sum(M.add, M.zero, U, λx:B. c(f(x)) • x) ∈ M.carrier",
						By(finiteU, termsM, module.ModuleSumIn.Read(moduleM).At(U, combination)))
					zero := b.Have(
						"f sends u and M.zero alike to N.zero, so u is M.zero",
						"module_sum(M.add, M.zero, U, λx:B. c(f(x)) • x) = M.zero",
						By(
							pullback,
							given[3],
							uIn,
							group.OneIn.Read(module.AddGroupOn.Read(moduleM)),
							module_homomorphism.HomZero.Read(linear),
							oneToOne.At(u, b.TermAs[B]("M.zero"))))
					cleared := b.Have(
						"S being independent, every coefficient c(f(x)) on U is zero",
						"∀x:B. x ∈ U ⇒ c(f(x)) = R.zero",
						By(
							finiteU,
							onU[0],
							scalarsU,
							zero,
							IndependentVanishingCombination.Read(independent).AsFact().At(
								U, b.TermAs[Fun[B, A]]("λx:B. c(f(x))"))))
					y := b.FixAs[C]("y")
					yInT := b.Assume()
					x, yIs := b.ObtainAs[B](
						"y is f(x) for some x of U",
						"∃x:B. y = f(x) ∧ x ∈ U",
						By(yInT, onU[1], set_basic.InImage.At(f, U, y)))
					atX := b.Conjuncts(
						yIs,
						"y = f(x)",
						"x lies in U")
					b.Show(
						"so c(y) = c(f(x)) is zero",
						By(Normalized, cleared.At(x), atX[0], atX[1]))
				}))
			a.Show(
				"the images lie in N, and only their zero combination vanishes",
				By(imagesInN, vanishing, ModuleIndependentDef.At(R, N, images)))
		}),
})}

// InjectiveImageBasis — a one-to-one linear map f carries a finite basis E
// of M to a finite basis of its image module, of the same size: f keeps E
// independent (IndependentImage) and carries its span, M, onto the image
// (HomSpan), and a map one-to-one on E keeps its count.
var InjectiveImageBasis = injectiveImageBasisThm{family.Add(registry.ProofEntry{
	Name: "InjectiveImageBasis",
	Key:  "prop_abe1b6b1e3fb3736",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀P:module_ops(A, C). ∀f:(B → C). ∀E:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, P, f)",
			"injective_on(M.carrier, f)",
			"finite(E)",
			"module_basis(R, M, E)",
		},
		Conclusion: "finite(image(f, E)) ∧ " +
			"module_basis(R, restrict_module(P, image(f, M.carrier)), image(f, E)) ∧ " +
			"card(image(f, E)) = card(E)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		P *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		E *Expr[Set[B]],
		assumptions Fact,
	) {
		parts := a.Conjuncts(
			assumptions,
			"f is linear",
			"f is injective on M",
			"E is finite",
			"E is a basis")
		modules := a.Have(
			"the homomorphism supplies both module structures",
			"module_on(R, M) ∧ module_on(R, P)",
			By(parts[0], module_homomorphism.ModuleHomomorphismDef.At(R, M, P, f)))
		moduleParts := a.Conjuncts(
			modules,
			"the source module laws",
			"the target module laws")
		basisData := a.Have(
			"E is independent and spans the source carrier",
			"module_independent(R, M, E) ∧ module_span(R, M, E) = M.carrier ∧ E ⊆ M.carrier",
			By(parts[3], ModuleBasisDef.At(R, M, E), IndependentInCarrier.At(R, M, E)))
		imageData := a.Have(
			"injectivity preserves independence and linearity preserves the span",
			"module_independent(R, P, image(f, E)) ∧ module_span(R, P, image(f, E)) = image(f, M.carrier)",
			By(
				Normalized,
				parts[0],
				parts[1],
				basisData,
				IndependentImage.At(R, M, P, f, E),
				HomSpan.At(R, M, P, f, E)))
		basis := a.Have(
			"the image basis is a basis of the full image module",
			"module_basis(R, restrict_module(P, image(f, M.carrier)), image(f, E))",
			By(
				module_homomorphism.ImageSubmodule.Read(parts[0]),
				imageData,
				At(
					BasisRestrict.Read(moduleParts[1]),
					a.TermAs[Set[C]]("image(f, M.carrier)"),
					a.TermAs[Set[C]]("image(f, E)"))))
		injectiveBasis := a.Have(
			"f is injective on the basis",
			"injective_on(E, f)",
			By(parts[1], basisData, functions.InjectiveOnSubset.At(f, E, a.TermAs[Set[B]]("M.carrier"))))
		count := a.Have(
			"the injective finite image has the same cardinality",
			"finite(image(f, E)) ∧ card(image(f, E)) = card(E)",
			By(parts[2], injectiveBasis, finite_set.FiniteImage.At(f, E), cardinality.CardImageInj.At(f, E)))
		a.Show(
			"the finite image basis has the original cardinality",
			By(count, basis))
	}),
})}

// IndependentImageKernel — a homomorphism is one-to-one on an independent
// set whose span meets the kernel only in zero, and carries it to an
// independent set: restricted to the span of S, f is a homomorphism whose
// kernel, the kernel of f inside the span, is {M.zero}, so it is one-to-one
// on the span and on S within it; and S is independent in the span, which
// the restricted f, one-to-one there, carries to an independent set
// (IndependentImage).
var IndependentImageKernel = independentImageKernelThm{family.Add(registry.ProofEntry{
	Name: "IndependentImageKernel",
	Key:  "prop_5104448fedfb86d5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"module_independent(R, M, S)",
			"group_kernel(N.zero, M.carrier, f) ∩ module_span(R, M, S) ⊆ {M.zero}",
		},
		Conclusion: "injective_on(S, f) ∧ module_independent(R, N, image(f, S))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"f is a homomorphism",
				"S is independent",
				"the kernel meets the span of S only in zero")
			linear, independent, meet := given[0], given[1], given[2]
			span := a.TermAs[Set[B]]("module_span(R, M, S)")
			restriction := a.TermAs[ModuleOps[A, B]]("restrict_module(M, module_span(R, M, S))")
			targetZero := a.TermAs[C]("N.zero")
			spanSub := a.Have(
				"the span of S, an independent part of M, is a submodule of M",
				"submodule(R, M, module_span(R, M, S))",
				By(
					IndependentInCarrier.Read(independent),
					submodule.SpanSubmodule.Read(module_homomorphism.HomSource.Read(linear)).At(S)))
			restricted := a.Have(
				"f restricted to the span of S is a homomorphism",
				"module_homomorphism(R, restrict_module(M, module_span(R, M, S)), N, f)",
				By(linear, spanSub, module_homomorphism.HomRestrictSource.At(R, M, N, f, span)))
			kernel := a.Have(
				"its kernel is the kernel of f inside the span, which is "+
					"{M.zero}: the span holds M.zero, which f sends to N.zero",
				"group_kernel(N.zero, module_span(R, M, S), f) = {M.zero}",
				BySets(
					meet,
					submodule.SubmoduleSubset.Read(spanSub),
					submodule.SubmoduleZero.Read(spanSub),
					module_homomorphism.HomZero.Read(linear),
					At(group_homomorphism.InKernel, targetZero, span, f),
					At(group_homomorphism.InKernel, targetZero, a.TermAs[Set[B]]("M.carrier"), f)))
			oneToOne := a.Have(
				"so the restricted f is one-to-one on the span of S",
				"injective_on(module_span(R, M, S), f)",
				By(restricted, kernel, module_homomorphism.KernelTrivialIffInjective.At(R, restriction, N, f)))
			sIndependent := a.Have(
				"S lies in its span and is independent in M, so it is independent in the restriction",
				"module_independent(R, restrict_module(M, module_span(R, M, S)), S)",
				By(
					independent,
					submodule.SubsetSpan.At(R, M, S),
					submodule.SubmoduleSubset.Read(spanSub),
					IndependentRestrict.At(R, M, span, S)))
			a.Show(
				"f is one-to-one on S within its span, and the restricted "+
					"f, one-to-one there, carries S to an independent set",
				By(
					oneToOne,
					submodule.SubsetSpan.At(R, M, S),
					functions.InjectiveOnSubset.At(f, S, span),
					restricted,
					sIndependent,
					IndependentImage.At(R, restriction, N, f, S)))
		}),
})}

// IndependentFromImage — a set that a homomorphism carries one to one
// onto an independent set is independent, and its span meets the kernel
// only in zero: a combination the map kills is carried to the combination
// of the images with the same coefficients, which independence of the
// images forces to be trivial.
var IndependentFromImage = independentFromImageThm{family.Add(registry.ProofEntry{
	Name: "IndependentFromImage",
	Key:  "prop_d28e48bc8b656aba",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"S ⊆ M.carrier",
			"injective_on(S, f)",
			"module_independent(R, N, image(f, S))",
		},
		Conclusion: "module_independent(R, M, S) ∧ " +
			"group_kernel(N.zero, M.carrier, f) ∩ module_span(R, M, S) ⊆ {M.zero}",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"f is a homomorphism",
				"S lies in M",
				"f is one-to-one on S",
				"f carries S to an independent set")
			linear, sInM, oneToOne, imageIndependent := given[0], given[1], given[2], given[3]
			moduleM := module_homomorphism.HomSource.Read(linear)
			moduleN := module_homomorphism.HomTarget.Read(linear)

			kills := a.Have(
				"a combination of S that f sends to zero has every coefficient zero",
				Statement{
					Binders: "∀T:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ S",
						"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
						"f(module_sum(M.add, M.zero, T, λx:B. a(x) • x)) = N.zero",
					},
					Conclusion: "∀x:B. x ∈ T ⇒ a(x) = R.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[B]]("T")
					coefficient := b.FixAs[Fun[B, A]]("a")
					parts := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T lies in S",
						"the coefficients are scalars",
						"f kills the combination")
					finiteT, tInS, scalars, killed := parts[0], parts[1], parts[2], parts[3]
					tInM := b.Have(
						"T lies in M",
						"T ⊆ M.carrier",
						BySets(tInS, sInM))
					oneToOneT := b.Have(
						"f is one-to-one on T",
						"injective_on(T, f)",
						By(oneToOne, tInS, functions.InjectiveOnSubset.At(f, T, S)))
					undo := b.Have(
						"so inverse_on undoes f on T",
						"∀x:B. x ∈ T ⇒ inverse_on(T, f, f(x)) = x",
						By(oneToOneT, functions.InverseOnLeft))
					images := b.Have(
						"f carries the combination to the combination of the images with the same coefficients",
						"module_sum(N.add, N.zero, T, λx:B. N.smul(a(x), f(x))) = N.zero",
						By(
							killed,
							finiteT,
							b.Unfolded(tInM, set_basic.SubsetDef),
							scalars,
							linear,
							module_homomorphism.HomCombination.At(R, M, N, f, T, coefficient, b.TermAs[Fun[B, B]]("λx:B. x"))))
					terms := b.Have(
						"each term of that combination is a vector of N",
						"∀x:B. x ∈ T ⇒ N.smul(a(x), f(x)) ∈ N.carrier",
						Derive(func(c *Argument) {
							x := c.FixAs[B]("x")
							xInT := c.Assume()
							xInM := c.Have(
								"x lies in M",
								"x ∈ M.carrier",
								BySets(xInT, tInM))
							c.Show(
								"a scalar times the image of a vector of M lies in N",
								By(
									scalars.At(x),
									xInT,
									xInM,
									linear,
									moduleN,
									module.SmulIn.At(R, N, c.TermAs[A]("a(x)"), f.Apply(x)),
									module_homomorphism.HomIn.At(R, M, N, f, x)))
						}))
					reindexed := b.Have(
						"read over the image of T, the combination of the "+
							"images has the coefficient of the preimage at each image",
						"module_sum(N.add, N.zero, image(f, T), λy:C. N.smul(a(inverse_on(T, f, y)), y)) = N.zero",
						By(
							finiteT,
							undo,
							terms,
							images,
							oneToOneT,
							linear,
							moduleN,
							module.ModuleSumImage.At(
								R, N, T, f, b.TermAs[Fun[C, C]]("λy:C. N.smul(a(inverse_on(T, f, y)), y)")),
							module.ModuleSumCongruence.At(
								b.TermAs[Fun2[C, C, C]]("N.add"),
								b.TermAs[C]("N.zero"),
								T,
								b.TermAs[Fun[B, C]]("λx:B. N.smul(a(inverse_on(T, f, f(x))), f(x))"),
								b.TermAs[Fun[B, C]]("λx:B. N.smul(a(x), f(x))"))))
					onImage := b.Have(
						"the coefficient at an image is a scalar",
						"∀y:C. y ∈ image(f, T) ⇒ a(inverse_on(T, f, y)) ∈ R.carrier",
						By(scalars, functions.InverseOnIn))
					vanish := b.Have(
						"the images are independent, so every coefficient at an image is zero",
						"∀y:C. y ∈ image(f, T) ⇒ a(inverse_on(T, f, y)) = R.zero",
						By(
							finiteT,
							onImage,
							reindexed,
							tInS,
							imageIndependent,
							At(
								IndependentVanishingCombination,
								R,
								N,
								b.TermAs[Set[C]]("image(f, S)"),
								b.TermAs[Set[C]]("image(f, T)"),
								b.TermAs[Fun[C, A]]("λy:C. a(inverse_on(T, f, y))")),
							finite_set.FiniteImage.At(f, T),
							set_image.ImageSubset.At(f, T, S)))
					b.Show(
						"and the coefficient at f(x) is the coefficient at x",
						By(undo, vanish, set_image.FunInImage))
				}))

			trivial := a.Have(
				"a combination of S equal to zero is sent to zero, so it is the trivial one",
				Statement{
					Binders: "∀T:set(B). ∀a:(B → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ S",
						"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
						"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero",
					},
					Conclusion: "∀x:B. x ∈ T ⇒ a(x) = R.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[B]]("T")
					coefficient := b.FixAs[Fun[B, A]]("a")
					zero := b.Assume()
					b.Show(
						"f sends zero to zero",
						By(Normalized, zero, kills.At(T, coefficient), module_homomorphism.HomZero.At(R, M, N, f), linear))
				}))
			independent := a.Have(
				"so S is independent",
				"module_independent(R, M, S)",
				By(sInM, trivial, ModuleIndependentDef.At(R, M, S)))

			meets := a.Have(
				"a member of the span of S that f kills is zero",
				"∀z:B. z ∈ module_span(R, M, S) ∧ f(z) = N.zero ⇒ z = M.zero",
				Derive(func(b *Argument) {
					z := b.FixAs[B]("z")
					parts := b.Conjuncts(
						b.Assume(),
						"z lies in the span of S",
						"f kills z")
					T, coefficient, combination := b.Obtain2As[Set[B], Fun[B, A]](
						"z is a combination of some finite T inside S",
						"∃T:set(B). ∃a:(B → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ S ∧ "+
							"    (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ "+
							"    z = module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
						By(parts[0], sInM, moduleM, SpanMembership.At(R, M, S, z)))
					pieces := b.Conjuncts(
						combination,
						"T is finite",
						"T lies in S",
						"the coefficients are scalars",
						"z is the combination")
					finiteT, tInS, scalars, zIs := pieces[0], pieces[1], pieces[2], pieces[3]
					vanish := b.Have(
						"f kills the combination, so its coefficients are zero",
						"∀x:B. x ∈ T ⇒ a(x) = R.zero",
						By(Normalized, kills.At(T, coefficient), finiteT, tInS, scalars, zIs, parts[1]))
					terms := b.Have(
						"so every term is zero",
						"∀x:B. x ∈ T ⇒ a(x) • x = M.zero",
						Derive(func(c *Argument) {
							x := c.FixAs[B]("x")
							xInT := c.Assume()
							xInM := c.Have(
								"x lies in M",
								"x ∈ M.carrier",
								BySets(xInT, tInS, sInM))
							c.Show(
								"the zero scalar kills x",
								By(Normalized, vanish.At(x), xInT, xInM, moduleM, module.ZeroSmul.At(R, M, x)))
						}))
					b.Show(
						"and z, their sum, is zero",
						By(
							Normalized,
							finiteT,
							terms,
							zIs,
							moduleM,
							module.ModuleSumZero.At(R, M, T, b.TermAs[Fun[B, B]]("λx:B. a(x) • x"))))
				}))
			kernelMeets := a.Have(
				"so the kernel meets the span of S only in zero",
				"group_kernel(N.zero, M.carrier, f) ∩ module_span(R, M, S) ⊆ {M.zero}",
				BySets(meets, group_homomorphism.InKernel))
			a.Show(
				"S is independent and its span meets the kernel only in zero",
				By(independent, kernelMeets))
		}),
})}

// BasisPullback — a basis of the image of a one-to-one homomorphism pulls
// back to a basis of its source. f carries the preimage of the basis one
// to one onto the basis, which is independent in N, so the preimage is
// independent (IndependentFromImage); and f carries the span of the
// preimage onto the span of the basis, which is the image of all of M, so
// injectivity makes that span all of M.
var BasisPullback = basisPullbackThm{family.Add(registry.ProofEntry{
	Name: "BasisPullback",
	Key:  "prop_e31a49b526ad4b3e",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀E:set(C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"injective_on(M.carrier, f)",
			"module_basis(R, restrict_module(N, image(f, M.carrier)), E)",
		},
		Conclusion: "module_basis(R, M, preimage_on(M.carrier, f, E))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			E *Expr[Set[C]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"f is a homomorphism",
				"f is one-to-one on M",
				"E is a basis of the image of f")
			linear, injective, basis := given[0], given[1], given[2]
			moduleM, moduleN :=
				module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
			carrier := a.TermAs[Set[B]]("M.carrier")
			image := a.TermAs[Set[C]]("image(f, M.carrier)")
			preimage := a.TermAs[Set[B]]("preimage_on(M.carrier, f, E)")
			span := a.TermAs[Set[B]]("module_span(R, M, preimage_on(M.carrier, f, E))")
			inN := a.Have(
				"E, a basis of the image, a submodule of N, is independent in N and spans the image there",
				"module_independent(R, N, E) ∧ module_span(R, N, E) = image(f, M.carrier)",
				By(
					basis,
					linear,
					module_homomorphism.ImageSubmodule.At(R, M, N, f),
					BasisRestrict.Read(moduleN).At(image, E)))
			ofBasis := a.Conjuncts(
				inN,
				"E is independent in N",
				"E spans the image")

			// The preimage is independent.
			onto := a.Have(
				"f carries the preimage of E onto E, which lies in the image",
				"image(f, preimage_on(M.carrier, f, E)) = E",
				BySets(ofBasis[1], submodule.SubsetSpan.At(R, N, E)))
			preimageInM := a.Have(
				"the preimage lies in M",
				"preimage_on(M.carrier, f, E) ⊆ M.carrier",
				BySets())
			oneToOne := a.Have(
				"and f is one-to-one on it",
				"injective_on(preimage_on(M.carrier, f, E), f)",
				By(injective, preimageInM, functions.InjectiveOnSubset.At(f, preimage, carrier)))
			independent := a.Have(
				"so the preimage, carried one to one onto the independent E, is independent",
				"module_independent(R, M, preimage_on(M.carrier, f, E))",
				By(linear, preimageInM, oneToOne, onto, ofBasis[0], IndependentFromImage.At(R, M, N, f, preimage)))

			// The preimage spans M.
			spanImage := a.Have(
				"f carries the span of the preimage onto the span of E, which is the image",
				"image(f, module_span(R, M, preimage_on(M.carrier, f, E))) = image(f, M.carrier)",
				CalcEq(
					Leg(
						a.TermAs[Set[C]]("module_span(R, N, image(f, preimage_on(M.carrier, f, E)))"),
						"f carries a span onto the span of the images",
						By(linear, preimageInM, HomSpan.At(R, M, N, f, preimage))),
					FinalLeg(
						"the images are E, which spans the image",
						By(Normalized, onto, ofBasis[1])),
				))
			spanInM := a.Have(
				"the span of the preimage lies in M",
				"module_span(R, M, preimage_on(M.carrier, f, E)) ⊆ M.carrier",
				By(preimageInM, submodule.SpanSubmodule.Read(moduleM).At(preimage), submodule.SubmoduleSubset))
			separated := a.Have(
				"f, one-to-one on M, tells subsets of M apart by their images",
				"∀s t:set(B). s ⊆ M.carrier ∧ t ⊆ M.carrier ∧ image(f, s) = image(f, t) ⇒ s = t",
				By(injective, set_image.InjectiveOnImage.At(f, carrier)))
			spans := a.Have(
				"so the span of the preimage, which f carries onto the image of M, is M",
				"module_span(R, M, preimage_on(M.carrier, f, E)) = M.carrier",
				By(separated.At(span, carrier), spanImage, spanInM, set_order.SubsetRefl.At(carrier)))
			a.Show(
				"the preimage is independent and spans M",
				By(independent, spans, ModuleBasisDef.At(R, M, preimage)))
		}),
})}

// ---------------------------------------------------------------------------
// Over a field: exchange, bases, replacement
// ---------------------------------------------------------------------------

// SolveForMember — over a field, a member of a combination lying in a
// submodule N lies in N when its coefficient is nonzero and the other
// members lie in N: the combination solved for it. The combination is
// a(w) • w plus the combination over the other members (ModuleSumDelete),
// a sum of multiples of members of N, so a(w) • w, the difference of two
// members of N, lies in N; and w is inv(a(w)) • (a(w) • w).
var SolveForMember = solveForMemberThm{family.Add(registry.ProofEntry{
	Name: "SolveForMember",
	Key:  "prop_f88b41444a48b4e2",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀N T:set(B). ∀a:(B → A). ∀w:B.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, N)",
			"finite(T)",
			"T ⊆ M.carrier",
			"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
			"module_sum(M.add, M.zero, T, λx:B. a(x) • x) ∈ N",
			"∀x:B. x ∈ T ∧ x ≠ w ⇒ x ∈ N",
			"w ∈ T",
			"a(w) ≠ R.zero",
		},
		Conclusion: "w ∈ N",
		Abbrev: Abbrev{
			{Name: "others", Text: "module_sum(M.add, M.zero, delete(T, w), λx:B. a(x) • x)"},
		},
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			N, T *Expr[Set[B]],
			a *Arrow[B, A],
			w *Expr[B],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"N is a submodule",
				"T is finite",
				"T lies in M",
				"a is a scalar on T",
				"the combination of a over T lies in N",
				"the members of T but w lie in N",
				"w lies in T",
				"the coefficient of w is not zero")
			scalarsField, isSubmodule, finT, tInM, scalars, sumInN, othersInN, wInT, nonzero :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6], given[7], given[8]
			fieldR := arg.Unfolded(scalarsField, field.RingSubfieldDef)
			inM := arg.Unfolded(tInM, set_basic.SubsetDef)
			combination := arg.TermAs[Fun[B, B]]("λx:B. a(x) • x")
			rest := arg.TermAs[Set[B]]("delete(T, w)")
			terms := arg.Have(
				"each term a(x) • x lies in M",
				"∀x:B. x ∈ T ⇒ a(x) • x ∈ M.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), scalars.At(x), module.SmulIn.Read(moduleOn))
				}))
			split := arg.Have(
				"the combination is a(w) • w plus the combination over the other members",
				"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = a(w) • w + «others»",
				By(finT, wInT, terms, module.ModuleSumDelete.Read(moduleOn).At(T, w, combination)))
			restTerms := arg.Have(
				"each term a(x) • x over the other members lies in N, N being closed under scaling",
				"∀x:B. x ∈ delete(T, w) ⇒ a(x) • x ∈ N",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(
						set_basic.InDelete.At(T, x, w),
						othersInN.At(x),
						scalars.At(x),
						submodule.SubmoduleSmul.Read(isSubmodule).AsFact().At(a.Apply(x), x))
				}))
			othersIn := arg.Have(
				"so their combination, a finite sum of vectors of the submodule N, lies in N",
				"«others» ∈ N",
				By(
					isSubmodule,
					finT,
					finite_set.FiniteDeleteImp.At(T, w),
					restTerms,
					submodule.SubmoduleModuleSum.Read(moduleOn).At(N, rest, combination)))
			wIn := arg.Have(
				"w lies in M",
				"w ∈ M.carrier",
				By(inM.At(w), wInT))
			coefIn := arg.Have(
				"a(w) is a scalar",
				"a(w) ∈ R.carrier",
				By(scalars.At(w), wInT))
			wM, coef := arg.MemberOf[on.M](w, wIn), arg.MemberOf[on.R](arg.TermAs[A]("a(w)"), coefIn)
			othersM := arg.MemberOf[on.M](arg.TermAs[B]("«others»"), arg.Have(
				"the combination over the other members lies in M, as N does",
				"«others» ∈ M.carrier",
				BySets(othersIn, submodule.SubmoduleSubset.Read(isSubmodule))))
			difference := arg.Have(
				"a(w) • w is the combination less the others",
				"a(w) • w = module_sum(M.add, M.zero, T, λx:B. a(x) • x) + -«others»",
				By(
					split,
					group.MulInvCancelRightOn.Read(module.AddGroupOn.Read(moduleOn)).At(
						othersM, module.SmulIn.Read(moduleOn).At(coef, wM))))
			termIn := arg.Have(
				"so a(w) • w, the difference of two members of N, lies in N",
				"a(w) • w ∈ N",
				By(
					difference,
					sumInN,
					othersIn,
					submodule.SubmoduleSub.Read(isSubmodule).AsFact().At(
						arg.TermAs[B]("module_sum(M.add, M.zero, T, λx:B. a(x) • x)"), arg.TermAs[B]("«others»"))))
			invIn := arg.Have(
				"a(w) has an inverse among the scalars",
				"inv(a(w)) ∈ R.carrier",
				By(coefIn, field.InvIn.Read(fieldR)))
			invCoef := arg.MemberOf[on.R](arg.TermAs[A]("inv(a(w))"), invIn)
			solved := arg.Have(
				"w is inv(a(w)) • (a(w) • w)",
				"w = inv(a(w)) • (a(w) • w)",
				CalcEq(
					Leg(
						arg.TermAs[B]("R.one • w"),
						"R.one fixes w",
						By(module.SmulOne.Read(moduleOn).At(wM))),
					Leg(
						arg.TermAs[B]("(inv(a(w)) * a(w)) • w"),
						"a(w) is not zero, so its inverse cancels it",
						By(
							Normalized,
							nonzero,
							field.MulLeftInverseOn.Read(fieldR).At(proof.MemberOf(arg.TermAs[A]("a(w)"), coefIn)))),
					FinalLeg(
						"scaling twice is scaling by the product",
						By(module.SmulMul.Read(moduleOn).At(invCoef, coef, wM))),
				))
			arg.Show(
				"so w, a multiple of a(w) • w, lies in N",
				By(
					Normalized,
					solved,
					invIn,
					termIn,
					submodule.SubmoduleSmul.Read(isSubmodule).AsFact().At(
						arg.TermAs[A]("inv(a(w))"), arg.TermAs[B]("a(w) • w"))))
		}),
})}

// IndependentInsertIff — over a field, a vector outside S joins S as an
// independent set exactly when S is independent and the vector lies
// outside its span. ⇒ is IndependentSubset and IndependentInsertOutsideSpan.
// ⇐: in a vanishing combination over a finite part T of insert(v, S), the
// coefficient at v is zero, since otherwise the combination, M.zero,
// solved for v would put v in the span of S (SolveForMember); so the
// combination is the one over T ∩ S, whose coefficients S's independence
// clears.
var IndependentInsertIff = independentInsertIffThm{family.Add(registry.ProofEntry{
	Name: "IndependentInsertIff",
	Key:  "prop_800068ec8bdc3e0a",
	Reading: "The field is load-bearing in ⇐: a vanishing combination with a " +
		"nonzero coefficient at v is solved for v by dividing by that coefficient; " +
		"⇒ needs only R.one ≠ R.zero. v ∉ S keeps v's coefficient apart from S's.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B). ∀v:B.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"S ⊆ M.carrier",
			"v ∈ M.carrier",
			"v ∉ S",
		},
		Conclusion: "module_independent(R, M, insert(v, S)) ⇔ " +
			"module_independent(R, M, S) ∧ v ∉ module_span(R, M, S)",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S lies in M",
				"v lies in M",
				"v lies outside S")
			scalarsField, sInM, vInM, vOutsideS := given[0], given[1], given[2], given[3]
			fieldR := arg.Unfolded(scalarsField, field.RingSubfieldDef)
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			carrier, extended := arg.TermAs[Set[B]]("M.carrier"), arg.TermAs[Set[B]]("insert(v, S)")
			span := arg.TermAs[Set[B]]("module_span(R, M, S)")
			vM := arg.MemberOf[on.M](v, vInM)

			arg.Iff()
			arg.Forward(
				"S is a part of insert(v, S), and v, joining S "+
					"independently from outside it, lies outside its span",
				func(b *Argument, independent Fact) {
					sInExtended := b.Have(
						"S lies in insert(v, S)",
						"S ⊆ insert(v, S)",
						BySets())
					sIndependent := b.Have(
						"so S is independent",
						"module_independent(R, M, S)",
						By(independent, sInExtended, IndependentSubset.At(R, M, extended, S)))
					outside := b.Have(
						"and over a field, where R.one ≠ R.zero, v lies outside the span of S",
						"v ∉ module_span(R, M, S)",
						By(
							field.OneNotZeroOn.Read(fieldR),
							independent,
							vOutsideS,
							IndependentInsertOutsideSpan.Read(moduleOn).At(S, v)))
					b.Show(
						"S is independent and v lies outside its span",
						By(sIndependent, outside))
				})

			arg.Backward(
				"a vanishing combination over a part of insert(v, S) has coefficient "+
					"zero at v, else v lies in the span; the rest is a combination of S",
				func(b *Argument, both Fact) {
					parts := b.Conjuncts(
						both,
						"S is independent",
						"v lies outside the span of S")
					sIndependent, outside := parts[0], parts[1]
					extendedInM := b.Have(
						"insert(v, S) lies in M",
						"insert(v, S) ⊆ M.carrier",
						By(vInM, sInM, set_order.InsertSubset.At(S, carrier, v)))
					spanSubmodule := b.Have(
						"the span of S is a submodule",
						"submodule(R, M, module_span(R, M, S))",
						By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S)))
					vanishing := b.Have(
						"a vanishing combination over a finite part of insert(v, S) has every coefficient R.zero",
						Statement{
							Binders: "∀T:set(B). ∀a:(B → A).",
							Hypotheses: []string{
								"finite(T)",
								"T ⊆ insert(v, S)",
								"∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier",
								"module_sum(M.add, M.zero, T, λx:B. a(x) • x) = M.zero",
							},
							Conclusion: "∀x:B. x ∈ T ⇒ a(x) = R.zero",
						},
						Derive(func(c *Argument) {
							T := c.FixAs[Set[B]]("T")
							a := c.FixAs[Fun[B, A]]("a")
							about := c.Conjuncts(
								c.Assume(),
								"T is finite",
								"T lies in insert(v, S)",
								"a is a scalar on T",
								"the combination of a over T vanishes")
							finT, tInExtended, scalars, vanishes := about[0], about[1], about[2], about[3]
							tInM := c.Have(
								"T lies in M",
								"T ⊆ M.carrier",
								By(tInExtended, extendedInM, set_order.SubsetTrans.At(T, extended, carrier)))
							atV := c.Have(
								"if v is in T, its coefficient is zero: else the "+
									"combination, M.zero, solved for v puts v in the span of S",
								"v ∈ T ⇒ a(v) = R.zero",
								Derive(func(d *Argument) {
									vInT := d.Assume()
									nonzero := d.SupposeNot()
									sumInSpan := d.Have(
										"the combination, M.zero, lies in the span of S",
										"module_sum(M.add, M.zero, T, λx:B. a(x) • x) ∈ module_span(R, M, S)",
										By(vanishes, submodule.SubmoduleZero.Read(spanSubmodule)))
									othersInSpan := d.Have(
										"the members of T but v lie in S, so in its span",
										"∀x:B. x ∈ T ∧ x ≠ v ⇒ x ∈ module_span(R, M, S)",
										BySets(tInExtended, submodule.SubsetSpan.At(R, M, S)))
									d.Show(
										"so v lies in the span of S, which it does not",
										By(
											scalarsField,
											spanSubmodule,
											finT,
											tInM,
											scalars,
											sumInSpan,
											othersInSpan,
											vInT,
											nonzero,
											outside,
											SolveForMember.Read(moduleOn).At(inv, span, T, a, v)))
								}))
							common := c.TermAs[Set[B]]("T ∩ S")
							inM := c.Unfolded(tInM, set_basic.SubsetDef)
							terms := c.Have(
								"each term a(x) • x over T lies in M",
								"∀x:B. x ∈ T ⇒ a(x) • x ∈ M.carrier",
								c.ForEach(func(x *Expr[B]) Action {
									return By(inM.At(x), scalars.At(x), module.SmulIn.Read(moduleOn))
								}))
							offS := c.Have(
								"a member of T outside S is v, whose term R.zero • v vanishes",
								"∀x:B. x ∈ T ∧ x ∉ T ∩ S ⇒ a(x) • x = M.zero",
								BySets(tInExtended, atV, module.ZeroSmul.Read(moduleOn).At(vM)))
							onCommon := c.Have(
								"so the combination over T is the one over T ∩ S, which vanishes",
								"module_sum(M.add, M.zero, T ∩ S, λx:B. a(x) • x) = M.zero",
								By(
									vanishes,
									finT,
									terms,
									offS,
									set_order.InterSubset.At(T, S),
									module.ModuleSumSupport.Read(moduleOn).At(T, common, c.TermAs[Fun[B, B]]("λx:B. a(x) • x"))))
							commonInS := c.Have(
								"T ∩ S lies in S",
								"T ∩ S ⊆ S",
								BySets())
							commonScalars := c.Have(
								"and a is a scalar on it",
								"∀x:B. x ∈ T ∩ S ⇒ a(x) ∈ R.carrier",
								BySets(scalars))
							cleared := c.Have(
								"S's independence clears a on T ∩ S",
								"∀x:B. x ∈ T ∩ S ⇒ a(x) = R.zero",
								By(
									Normalized,
									finT,
									finite_set.FiniteInter.At(T, S),
									commonInS,
									commonScalars,
									onCommon,
									IndependentVanishingCombination.Read(sIndependent).AsFact().At(common, a)))
							c.Show(
								"so a vanishes on T: on T ∩ S, and at v, its one member outside S",
								c.ForEach(func(x *Expr[B]) Action {
									return BySets(tInExtended, cleared.At(x), atV)
								}))
						}))
					b.Show(
						"so insert(v, S) is independent",
						By(extendedInM, vanishing, ModuleIndependentDef.At(R, M, extended)))
				})
		}),
})}

// Exchange — over a field, a vector v of the span of insert(w, S) that
// is not in the span of S puts w in the span of insert(v, S). The span
// of insert(w, S) is a submodule of M, so v lies in M. The vector v is
// c • w + u for a scalar c and a u in the span of S (SpanInsert); c is
// not zero, since v lies outside that span; so w is inv(c) • (v + -u),
// and the span of insert(v, S), a submodule holding v and the span of
// S, holds it.
var Exchange = exchangeThm{family.Add(registry.ProofEntry{
	Name: "Exchange",
	Key:  "prop_1a52ef61ccd92e41",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B). ∀v w:B.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"S ⊆ M.carrier",
			"w ∈ M.carrier",
			"v ∈ module_span(R, M, insert(w, S))",
			"v ∉ module_span(R, M, S)",
		},
		Conclusion: "w ∈ module_span(R, M, insert(v, S))",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			v, w *Expr[B],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S lies in M",
				"w lies in M",
				"v lies in the span of insert(w, S)",
				"v lies outside the span of S")
			scalarsField, sInM, wInM, vInSpan, outside := given[0], given[1], given[2], given[3], given[4]
			fieldR := arg.Unfolded(scalarsField, field.RingSubfieldDef)
			additive := module.AddGroupOn.Read(moduleOn)
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			carrier := arg.TermAs[Set[B]]("M.carrier")
			insertWS, insertVS := arg.TermAs[Set[B]]("insert(w, S)"), arg.TermAs[Set[B]]("insert(v, S)")
			wM := arg.MemberOf[on.M](w, wInM)
			spanOfWS := arg.Have(
				"insert(w, S) lies in M, so its span is a submodule",
				"submodule(R, M, module_span(R, M, insert(w, S)))",
				By(
					wInM,
					sInM,
					set_order.InsertSubset.At(S, carrier, w),
					submodule.SpanSubmodule.Read(moduleOn).At(insertWS)))
			vInM := arg.Have(
				"v lies in M, as the span of insert(w, S) does",
				"v ∈ M.carrier",
				BySets(vInSpan, submodule.SubmoduleSubset.Read(spanOfWS)))

			c, u, written := arg.Obtain2As[A, B](
				"v, in the span of insert(w, S), is c • w + u for a scalar c and a u in the span of S",
				"∃c:A. ∃u:B. c ∈ R.carrier ∧ u ∈ module_span(R, M, S) ∧ v = c • w + u",
				BySets(vInSpan, sInM, submodule.SpanInsert.Read(moduleOn).At(S, wM)))
			parts := arg.Conjuncts(
				written,
				"c is a scalar",
				"u lies in the span of S",
				"v is c • w + u")
			coefIn, uInSpan, decomposition := parts[0], parts[1], parts[2]
			spanOfS := arg.Have(
				"the span of S is a submodule",
				"submodule(R, M, module_span(R, M, S))",
				By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S)))
			uM := arg.MemberOf[on.M](u, arg.Have(
				"u lies in M, as the span of S does",
				"u ∈ M.carrier",
				BySets(uInSpan, submodule.SubmoduleSubset.Read(spanOfS))))
			cM := arg.MemberOf[on.R](c, coefIn)
			// The field read off ring_subfield is typed at no carrier, so c
			// enters its laws as a member of no named carrier.
			cField := proof.MemberOf(c, coefIn)

			nonzero := arg.Have(
				"c is not zero: else v = R.zero • w + u = u would lie in the span of S",
				"c ≠ R.zero",
				By(
					Normalized,
					outside,
					decomposition,
					uInSpan,
					module.ZeroSmul.Read(moduleOn).At(wM),
					group.LeftIdentityOn.Read(additive).At(uM)))
			inverse := inv.Apply(c)
			invIn := arg.Have(
				"c has an inverse among the scalars",
				"inv(c) ∈ R.carrier",
				By(coefIn, field.InvIn.Read(fieldR)))
			inverseM := arg.MemberOf[on.R](inverse, invIn)
			solved := arg.Have(
				"so w is inv(c) • (v + -u)",
				"w = inv(c) • (v + -u)",
				CalcEq(
					Leg(
						arg.TermAs[B]("R.one • w"),
						"R.one fixes w",
						By(module.SmulOne.Read(moduleOn).At(wM))),
					Leg(
						arg.TermAs[B]("(inv(c) * c) • w"),
						"c is not zero, so its inverse cancels it",
						By(Normalized, nonzero, field.MulLeftInverseOn.Read(fieldR).At(cField))),
					Leg(
						arg.TermAs[B]("inv(c) • (c • w)"),
						"scaling twice is scaling by the product",
						By(module.SmulMul.Read(moduleOn).At(inverseM, cM, wM))),
					FinalLeg(
						"c • w is v less u",
						By(
							Normalized,
							decomposition,
							group.MulInvCancelRightOn.Read(additive).At(uM, module.SmulIn.Read(moduleOn).At(cM, wM)))),
				))

			spanOfVS := arg.Have(
				"insert(v, S) lies in M, so its span is a submodule",
				"submodule(R, M, module_span(R, M, insert(v, S)))",
				By(
					vInM,
					sInM,
					set_order.InsertSubset.At(S, carrier, v),
					submodule.SpanSubmodule.Read(moduleOn).At(insertVS)))
			vuInSpan := arg.Have(
				"v and u lie in the span of insert(v, S), which holds insert(v, S) and the span of S",
				"v ∈ module_span(R, M, insert(v, S)) ∧ u ∈ module_span(R, M, insert(v, S))",
				BySets(uInSpan, submodule.SubsetSpan.At(R, M, insertVS), submodule.SpanMono.At(R, M, S, insertVS)))
			arg.Show(
				"so it holds v + -u and its multiple by inv(c), which is w",
				BySets(
					solved,
					invIn,
					vuInSpan,
					submodule.SubmoduleSub.Read(spanOfVS).AsFact().At(v, u),
					submodule.SubmoduleSmul.Read(spanOfVS).AsFact().At(inverse, arg.TermAs[B]("v + -u"))))
		}),
})}

// MaximalIndependentBasis — over a field, an independent set to which no
// vector of M can be added independently is a basis. Its span is a
// submodule of M, so lies in M; and a vector of M outside the span lies
// outside S, so joins S independently (IndependentInsertIff), and the
// maximality of S would put it in S, inside the span.
var MaximalIndependentBasis = maximalIndependentBasisThm{family.Add(registry.ProofEntry{
	Name: "MaximalIndependentBasis",
	Key:  "prop_6d1f755affb72536",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_independent(R, M, S)",
			"∀v:B. v ∈ M.carrier ∧ module_independent(R, M, insert(v, S)) ⇒ v ∈ S",
		},
		Conclusion: "module_basis(R, M, S)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is independent",
				"a vector of M that joins S independently lies in S")
			scalarsField, independent, maximal := given[0], given[1], given[2]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			span, carrier := a.TermAs[Set[B]]("module_span(R, M, S)"), a.TermAs[Set[B]]("M.carrier")
			sInM := a.Have(
				"an independent set lies in M",
				"S ⊆ M.carrier",
				By(IndependentInCarrier.Read(independent)))
			spanInM := a.Have(
				"the span of S is a submodule of M, so it lies in M",
				"module_span(R, M, S) ⊆ M.carrier",
				By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S), submodule.SubmoduleSubset.At(R, M, span)))
			spanHoldsS := a.Unfolded(submodule.SubsetSpan.At(R, M, S), set_basic.SubsetDef)
			mInSpan := a.Have(
				"every vector of M lies in the span of S",
				"M.carrier ⊆ module_span(R, M, S)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					vM := b.MemberOf[on.M](v, b.Assume())
					outside := b.SupposeNot()
					notInS := b.Have(
						"S lies in its span, so v lies outside S",
						"v ∉ S",
						By(outside, spanHoldsS.At(v)))
					joins := b.Have(
						"outside the span, v joins the independent set S independently",
						"module_independent(R, M, insert(v, S))",
						By(
							scalarsField,
							sInM,
							notInS,
							independent,
							outside,
							IndependentInsertIff.Read(moduleOn).At(inv, S, vM)))
					b.Show(
						"yet the maximality of S then puts v in S",
						By(notInS, maximal.At(v), vM, joins))
				}))
			spansM := a.Have(
				"the two inclusions make the span of S all of M",
				"module_span(R, M, S) = M.carrier",
				By(spanInM, mInSpan, set_order.SubsetAntisym.At(span, carrier)))
			a.Show(
				"S is independent and spans M, so it is a basis",
				By(independent, spansM, ModuleBasisDef.At(R, M, S)))
		}),
})}

// BasisBetween — over a field, an independent set S inside a spanning set
// U extends to a basis between them: Zorn's lemma at inclusion over the
// family F of the independent sets between S and U. F holds S, and the
// union of a non-empty chain of its members is independent and lies
// between S and U, so F has a member E that no other member contains. A
// vector v of U outside the span of E would join E independently
// (IndependentInsertIff), and insert(v, E), a member of F containing E,
// would be E; so U lies in the span of E, a submodule, which then holds
// the span of U, all of M.
var BasisBetween = basisBetweenThm{family.Add(registry.ProofEntry{
	Name: "BasisBetween",
	Key:  "prop_88707b79b0b21f5e",
	Reading: "The axiom of choice enters here, through Zorn's lemma; no " +
		"finiteness is assumed, so the basis may be infinite. U ⊆ M.carrier " +
		"need not be assumed: U lies in its span, which is M.carrier.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S U:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_independent(R, M, S)",
			"S ⊆ U",
			"module_span(R, M, U) = M.carrier",
		},
		Conclusion: "∃E:set(B). S ⊆ E ∧ E ⊆ U ∧ module_basis(R, M, E)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S, U *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is independent",
				"S lies in U",
				"U spans M")
			scalarsField, independent, sInU, spansM := given[0], given[1], given[2], given[3]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			carrier := a.TermAs[Set[B]]("M.carrier")
			uInM := a.Have(
				"U lies in its span, which is M",
				"U ⊆ M.carrier",
				By(Normalized, spansM, submodule.SubsetSpan.At(R, M, U)))

			F, familyDef := a.LetAs[Set[Set[B]]](
				"F", "{T:set(B) | S ⊆ T ∧ T ⊆ U ∧ module_independent(R, M, T)}")
			inF := a.Have(
				"the members of F are the independent sets between S and U",
				"∀T:set(B). T ∈ F ⇔ S ⊆ T ∧ T ⊆ U ∧ module_independent(R, M, T)",
				BySets(familyDef))
			sInF := a.Have(
				"S is a member: it holds itself, lies in U and is independent",
				"S ∈ F",
				By(independent, sInU, set_order.SubsetRefl.At(S), inF.At(S)))
			nonEmpty := a.Have(
				"so F is not empty",
				"F ≠ ∅",
				By(Normalized, sInF, set_basic.MemberNotEmpty.At(F)))
			chainUnions := a.Have(
				"F contains the union of each of its non-empty chains",
				"∀G:set(set(B)). G ⊆ F ∧ G ≠ ∅ ∧ (∀s t:set(B). s ∈ G ∧ t ∈ G ⇒ s ⊆ t ∨ t ⊆ s) ⇒ ⋃G ∈ F",
				Derive(func(b *Argument) {
					G := b.FixAs[Set[Set[B]]]("G")
					union := b.TermAs[Set[B]]("⋃G")
					about := b.Conjuncts(
						b.Assume(),
						"G is a part of F",
						"G is not empty",
						"any two members of G are comparable")
					partOfF, gNonEmpty, gIsChain := about[0], about[1], about[2]
					inFamily := b.Unfolded(partOfF, set_basic.SubsetDef)
					members := b.Have(
						"each member of G is an independent set between S and U",
						"∀T:set(B). T ∈ G ⇒ S ⊆ T ∧ T ⊆ U ∧ module_independent(R, M, T)",
						b.ForEach(func(T *Expr[Set[B]]) Action {
							return By(inFamily.At(T), inF.At(T))
						}))
					unionIndependent := b.Have(
						"the union of a chain of independent sets is independent",
						"module_independent(R, M, ⋃G)",
						By(members, gIsChain, IndependentChainUnion.At(R, M, G)))
					g, gInG := b.ObtainAs[Set[B]](
						"G has a member g",
						"∃g:set(B). g ∈ G",
						By(gNonEmpty, set_basic.MemberNotEmpty.At(G)))
					sInUnion := b.Have(
						"the union holds S, which lies in g",
						"S ⊆ ⋃G",
						By(
							gInG,
							members.At(g),
							set_order.MemberSubsetUnions.At(G, g),
							set_order.SubsetTrans.At(S, g, union)))
					b.Show(
						"so the union, lying in U, is a member of F",
						By(unionIndependent, members, set_order.UnionsSubset.At(G, U), sInUnion, inF.At(union)))
				}))

			E, atE := a.ObtainAs[Set[B]](
				"so F has a member E that no other member contains: Zorn's lemma",
				"∃E:set(B). E ∈ F ∧ (∀T:set(B). T ∈ F ∧ E ⊆ T ⇒ T = E)",
				By(nonEmpty, chainUnions, order.ZornFamily.At(F)))
			aboutE := a.Conjuncts(
				atE,
				"E is a member of F",
				"every member of F that contains E is E")
			eInF, maximal := aboutE[0], aboutE[1]
			onE := a.Conjuncts(
				a.Have(
					"E lies between S and U and is independent",
					"S ⊆ E ∧ E ⊆ U ∧ module_independent(R, M, E)",
					By(eInF, inF.At(E))),
				"E holds S",
				"E lies in U",
				"E is independent")
			sInE, eInU, eIndependent := onE[0], onE[1], onE[2]
			eInM := a.Have(
				"so E lies in M",
				"E ⊆ M.carrier",
				By(eInU, uInM, set_order.SubsetTrans.At(E, U, carrier)))
			inSpan := a.Unfolded(submodule.SubsetSpan.At(R, M, E), set_basic.SubsetDef)

			spanned := a.Have(
				"each vector of U lies in the span of E: else E with it added would be a larger member of F",
				"U ⊆ module_span(R, M, E)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					vInU := b.Assume()
					outside := b.SupposeNot()
					notInE := b.Have(
						"E lies in its span, so v is not in E",
						"v ∉ E",
						By(outside, inSpan.At(v)))
					vM := b.MemberOf[on.M](v, b.Have(
						"v lies in M, as U does",
						"v ∈ M.carrier",
						BySets(vInU, uInM)))
					grown := b.TermAs[Set[B]]("insert(v, E)")
					grownIndependent := b.Have(
						"over a field, E with v added is independent, v lying outside the span of E",
						"module_independent(R, M, insert(v, E))",
						By(
							scalarsField,
							eInM,
							notInE,
							eIndependent,
							outside,
							IndependentInsertIff.Read(moduleOn).At(inv, E, vM)))
					above := b.Have(
						"it contains E",
						"E ⊆ insert(v, E)",
						BySets())
					member := b.Have(
						"so it holds S, and it lies in U, as v and E do: a member of F",
						"insert(v, E) ∈ F",
						By(
							grownIndependent,
							sInE,
							above,
							set_order.SubsetTrans.At(S, E, grown),
							vInU,
							eInU,
							set_order.InsertSubset.At(E, U, v),
							inF.At(grown)))
					same := b.Have(
						"a member of F containing E is E",
						"insert(v, E) = E",
						By(member, above, maximal.At(grown)))
					b.Show(
						"then v, a member of insert(v, E), lies in E, which it does not",
						By(Normalized, notInE, same, set_basic.InInsert.At(E, v, v)))
				}))

			spanE := a.TermAs[Set[B]]("module_span(R, M, E)")
			spanSubmodule := a.Have(
				"the span of E, a subset of M, is a submodule",
				"submodule(R, M, module_span(R, M, E))",
				By(eInM, submodule.SpanSubmodule.Read(moduleOn).At(E)))
			covers := a.Have(
				"a submodule holding U holds the span of U, which is M",
				"M.carrier ⊆ module_span(R, M, E)",
				By(Normalized, spanned, spansM, spanSubmodule, submodule.SpanLeast.At(R, M, U, spanE)))
			spansE := a.Have(
				"and the span of E, a submodule, lies in M: the two are one set",
				"module_span(R, M, E) = M.carrier",
				By(
					covers,
					submodule.SubmoduleSubset.Read(spanSubmodule),
					set_order.SubsetAntisym.At(spanE, carrier)))
			a.Take(E)
			a.Show(
				"E lies between S and U, and is independent and spans M: a basis",
				By(sInE, eInU, eIndependent, spansE, ModuleBasisDef.At(R, M, E)))
		}),
})}

// BasisExtends — over a field, every independent set lies in a basis:
// BasisBetween with M's carrier as the spanning set, a submodule and so
// its own span.
var BasisExtends = basisExtendsThm{family.Add(registry.ProofEntry{
	Name: "BasisExtends",
	Key:  "prop_a340cac7ab3c6a9",
	Reading: "The axiom of choice enters through BasisBetween's Zorn's " +
		"lemma; no finiteness is assumed, so the basis may be infinite.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_independent(R, M, S)",
		},
		Conclusion: "∃E:set(B). S ⊆ E ∧ module_basis(R, M, E)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is independent")
			scalarsField, independent := given[0], given[1]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			carrier := a.TermAs[Set[B]]("M.carrier")
			a.Show(
				"M's carrier, a submodule, is its own span, so a basis lies between S and that carrier",
				By(
					scalarsField,
					independent,
					IndependentInCarrier.Read(independent),
					submodule.CarrierSubmodule.Read(moduleOn),
					submodule.SpanOfSubmodule.At(R, M, carrier),
					BasisBetween.Read(moduleOn).At(inv, S, carrier)))
		}),
})}

// BasisExists — over a field, every module on a set has a basis: the
// empty set is independent, and an independent set lies in a basis.
var BasisExists = basisExistsThm{family.Add(registry.ProofEntry{
	Name: "BasisExists",
	Key:  "prop_511ccd8818c126a",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
		},
		Conclusion: "∃E:set(B). module_basis(R, M, E)",
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], inv *Arrow[A, A], scalarsField Fact) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			a.Show(
				"the empty set is independent, so some basis holds it",
				By(
					Normalized,
					scalarsField,
					IndependentEmpty.At(R, M),
					BasisExtends.Read(moduleOn).At(inv, a.TermAs[Set[B]]("∅"))))
		}),
})}

// BasisWithinSpanning — over a field, a spanning set holds a basis:
// BasisBetween from the empty set, which is independent and lies in S.
var BasisWithinSpanning = basisWithinSpanningThm{family.Add(registry.ProofEntry{
	Name:    "BasisWithinSpanning",
	Key:     "prop_61e674a10c19c49b",
	Reading: "S ⊆ M.carrier need not be assumed: S lies in its span, which is M.carrier.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_span(R, M, S) = M.carrier",
		},
		Conclusion: "∃E:set(B). E ⊆ S ∧ module_basis(R, M, E)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S spans M")
			scalarsField, spansM := given[0], given[1]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			a.Show(
				"the empty set is independent and lies in S, so a basis lies between ∅ and S",
				By(
					scalarsField,
					spansM,
					IndependentEmpty.At(R, M),
					set_order.EmptySubset.At(S),
					BasisBetween.Read(moduleOn).At(inv, a.TermAs[Set[B]]("∅"), S)))
		}),
})}

// ReplacementStep — over a field, a member v of an independent set I
// inside the span of S, v not in S, replaces some w of S outside I
// without losing I from the span: v is a combination of S, and some w of
// it outside I has a nonzero coefficient — else v would be a combination
// of the rest of I, outside whose span it lies
// (IndependentInsertOutsideSpan) — so the combination solved for w puts w
// in the span of insert(v, S ∖ {w}) (SolveForMember), and with it S, its
// span and I.
var ReplacementStep = replacementStepThm{family.Add(registry.ProofEntry{
	Name: "ReplacementStep",
	Key:  "prop_3c1326218f442cf5",
	Reading: "The exchange need not leave v outside span(S ∖ {w}): S need not be independent, " +
		"so the step is not an instance of Exchange, which asks v to lie outside that span.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S I:set(B). ∀v:B.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"S ⊆ M.carrier",
			"module_independent(R, M, I)",
			"I ⊆ module_span(R, M, S)",
			"v ∈ I",
			"v ∉ S",
		},
		Conclusion: "∃w:B. w ∈ S ∧ w ∉ I ∧ I ⊆ module_span(R, M, insert(v, S ∖ {w}))",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S, I *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S lies in M",
				"I is independent",
				"the span of S holds I",
				"v lies in I",
				"v lies outside S")
			scalarsField, sInM, independent, spannedByS, vInI, vOutsideS :=
				given[0], given[1], given[2], given[3], given[4], given[5]
			fieldR := arg.Unfolded(scalarsField, field.RingSubfieldDef)
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			carrier := arg.TermAs[Set[B]]("M.carrier")
			iInM := arg.Have(
				"I, being independent, lies in M",
				"I ⊆ M.carrier",
				By(IndependentInCarrier.Read(independent)))
			vInM := arg.Have(
				"so v lies in M",
				"v ∈ M.carrier",
				BySets(iInM, vInI))

			vInSpanS := arg.Have(
				"v lies in the span of S",
				"v ∈ module_span(R, M, S)",
				BySets(spannedByS, vInI))
			T, a, vIs := arg.Obtain2As[Set[B], Fun[B, A]](
				"so v is a combination over some finite T ⊆ S",
				"∃T:set(B). ∃a:(B → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ S ∧ "+
					"    (∀x:B. x ∈ T ⇒ a(x) ∈ R.carrier) ∧ "+
					"    v = module_sum(M.add, M.zero, T, λx:B. a(x) • x)",
				By(vInSpanS, sInM, SpanMembership.Read(moduleOn).At(S, v)))
			about := arg.Conjuncts(
				vIs,
				"T is finite",
				"T lies in S",
				"a is a scalar on T",
				"v is the combination of a over T")
			finT, tInS, scalars, vIsSum := about[0], about[1], about[2], about[3]
			tInM := arg.Have(
				"T lies in M, as S does",
				"T ⊆ M.carrier",
				By(tInS, sInM, set_order.SubsetTrans.At(T, S, carrier)))
			inM := arg.Unfolded(tInM, set_basic.SubsetDef)
			terms := arg.Have(
				"each term a(x) • x lies in M",
				"∀x:B. x ∈ T ⇒ a(x) • x ∈ M.carrier",
				arg.ForEach(func(x *Expr[B]) Action {
					return By(inM.At(x), scalars.At(x), module.SmulIn.Read(moduleOn))
				}))

			w, pivot := arg.ObtainAs[B](
				"some w of T outside I has a nonzero coefficient: else v is a combination of the rest of I",
				"∃w:B. w ∈ T ∧ w ∉ I ∧ a(w) ≠ R.zero",
				Derive(func(b *Argument) {
					none := b.SupposeNot()
					common, others := b.TermAs[Set[B]]("T ∩ I"), b.TermAs[Set[B]]("I ∖ {v}")
					vanish := b.Have(
						"then each term over T off I is R.zero • x, the zero vector",
						"∀x:B. x ∈ T ∧ x ∉ T ∩ I ⇒ a(x) • x = M.zero",
						b.ForEach(func(x *Expr[B]) Action {
							return By(
								none,
								set_basic.InInter.At(T, I, x),
								inM.At(x),
								module.ZeroSmul.Read(moduleOn).AsFact().At(x))
						}))
					onCommon := b.Have(
						"so v is the combination of a over T ∩ I",
						"v = module_sum(M.add, M.zero, T ∩ I, λx:B. a(x) • x)",
						By(
							vIsSum,
							finT,
							terms,
							vanish,
							set_order.InterSubset.At(T, I),
							module.ModuleSumSupport.Read(moduleOn).At(T, common, b.TermAs[Fun[B, B]]("λx:B. a(x) • x"))))
					commonInOthers := b.Have(
						"T ∩ I lies in I ∖ {v}, v lying outside S and so outside T",
						"T ∩ I ⊆ I ∖ {v}",
						BySets(tInS, vOutsideS))
					commonScalars := b.Have(
						"a is a scalar on T ∩ I",
						"∀x:B. x ∈ T ∩ I ⇒ a(x) ∈ R.carrier",
						BySets(scalars))
					b.Have(
						"I ∖ {v} lies in M",
						"I ∖ {v} ⊆ M.carrier",
						BySets(iInM))
					inOthers := b.Have(
						"so v lies in the span of I ∖ {v}",
						"v ∈ module_span(R, M, I ∖ {v})",
						Simp(Fwd(SpanMembership.Read(moduleOn))),
						Derive(func(c *Argument) {
							c.Take(common)
							c.Take(a)
							c.Show(
								"T ∩ I is a finite part of I ∖ {v} on which a is a scalar",
								By(finT, finite_set.FiniteInter.At(T, I), commonInOthers, commonScalars, onCommon))
						}))
					whole := b.Have(
						"v lies in I, so I is v laid into I ∖ {v}",
						"insert(v, I ∖ {v}) = I",
						BySets(vInI))
					vFresh := b.Have(
						"and v is not in I ∖ {v}",
						"v ∉ I ∖ {v}",
						BySets())
					b.Show(
						"but v joins I ∖ {v} as the independent set I, so over a field it lies outside the span of I ∖ {v}",
						By(
							inOthers,
							whole,
							vFresh,
							independent,
							field.OneNotZeroOn.Read(fieldR),
							IndependentInsertOutsideSpan.Read(moduleOn).At(others, v)))
				}))
			chosen := arg.Conjuncts(
				pivot,
				"w lies in T",
				"w lies outside I",
				"the coefficient of w is not zero")
			wInT, wOutsideI, nonzero := chosen[0], chosen[1], chosen[2]

			exchanged, newSpan :=
				arg.TermAs[Set[B]]("insert(v, S ∖ {w})"),
				arg.TermAs[Set[B]]("module_span(R, M, insert(v, S ∖ {w}))")
			exchangedInM := arg.Have(
				"insert(v, S ∖ {w}) lies in M",
				"insert(v, S ∖ {w}) ⊆ M.carrier",
				BySets(vInM, sInM))
			isSubmodule := arg.Have(
				"so its span is a submodule",
				"submodule(R, M, module_span(R, M, insert(v, S ∖ {w})))",
				By(exchangedInM, submodule.SpanSubmodule.Read(moduleOn).At(exchanged)))
			spans := submodule.SubsetSpan.At(R, M, exchanged)
			vInNew := arg.Have(
				"that span holds v",
				"v ∈ module_span(R, M, insert(v, S ∖ {w}))",
				BySets(spans))
			sumInNew := arg.Have(
				"so it holds the combination of a over T, which is v",
				"module_sum(M.add, M.zero, T, λx:B. a(x) • x) ∈ module_span(R, M, insert(v, S ∖ {w}))",
				By(Normalized, vIsSum, vInNew))
			othersInNew := arg.Have(
				"and so do the members of T but w, which lie in S ∖ {w}",
				"∀x:B. x ∈ T ∧ x ≠ w ⇒ x ∈ module_span(R, M, insert(v, S ∖ {w}))",
				BySets(tInS, spans))
			wInNew := arg.Have(
				"solved for w, whose coefficient is not zero, the combination puts w in that span",
				"w ∈ module_span(R, M, insert(v, S ∖ {w}))",
				By(
					scalarsField,
					isSubmodule,
					finT,
					tInM,
					scalars,
					sumInNew,
					othersInNew,
					wInT,
					nonzero,
					SolveForMember.Read(moduleOn).At(inv, newSpan, T, a, w)))

			sInNew := arg.Have(
				"S lies in that span: w does, and the rest of S lies in insert(v, S ∖ {w})",
				"S ⊆ module_span(R, M, insert(v, S ∖ {w}))",
				BySets(wInNew, spans))
			spanS := arg.TermAs[Set[B]]("module_span(R, M, S)")
			spanInNew := arg.Have(
				"hence so does the span of S, the least submodule holding S",
				"module_span(R, M, S) ⊆ module_span(R, M, insert(v, S ∖ {w}))",
				By(isSubmodule, sInNew, submodule.SpanLeast.At(R, M, S, newSpan)))
			wInS := arg.Have(
				"w lies in S, as T does",
				"w ∈ S",
				BySets(wInT, tInS))
			arg.Take(w)
			arg.Show(
				"w is a member of S outside I, and the span of "+
					"insert(v, S ∖ {w}) holds the span of S, which holds I",
				By(wInS, wOutsideI, spannedByS, spanInNew, set_order.SubsetTrans.At(I, spanS, newSpan)))
		}),
})}

// Steinitz — the replacement theorem: over a field, an independent set
// inside the span of a finite set S is finite and no larger than S.
// Strong induction on how many members of the spanning set lie outside
// I, the spanning set varying: when I lies inside it, I is a subset of
// a finite set; otherwise a member v of I outside it replaces a member
// w outside I, which keeps the set's size and its span's hold on I and
// leaves one member fewer outside I.
var Steinitz = steinitzThm{family.Add(registry.ProofEntry{
	Name: "Steinitz",
	Key:  "prop_7d63bd041d72cfe6",
	Reading: "S ⊆ M.carrier is load-bearing: otherwise the span of S is " +
		"𝕌 and admits an infinite independent I. finite(I) is not assumed; " +
		"it comes out of the case where I lies inside the spanning set.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀S I:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"finite(S)",
			"S ⊆ M.carrier",
			"module_independent(R, M, I)",
			"I ⊆ module_span(R, M, S)",
		},
		Conclusion: "finite(I) ∧ card(I) ≤ card(S)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			S, I *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"S is finite",
				"S lies in M",
				"I is independent",
				"the span of S holds I")
			scalarsField, finiteS, sInM, independent, spannedByS :=
				given[0], given[1], given[2], given[3], given[4]

			bounded := a.TermAs[Set[Nat]](
				"λn:num. ∀T:set(B). " +
					"    finite(T) ∧ T ⊆ M.carrier ∧ I ⊆ module_span(R, M, T) ∧ card(T ∖ I) = n ⇒ " +
					"    finite(I) ∧ card(I) ≤ card(T)")
			a.Show(
				"strong induction on the members of a finite spanning set "+
					"outside I carries the bound to every such set, S among them",
				ByInduction(At(
					nat_order.StrongInduction, bounded, a.TermAs[Nat]("card(S ∖ I)")), finiteS, sInM, spannedByS,
					Case(
						"granted the bound for spanning sets with fewer members outside I, a T with n of them bounds I",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							fewer := b.Assume()
							T := b.FixAs[Set[B]]("T")
							onT := b.Conjuncts(
								b.Assume(),
								"T is finite",
								"T lies in M",
								"the span of T holds I",
								"n members of T lie outside I")
							finiteT, tInM, spannedByT, outsideT := onT[0], onT[1], onT[2], onT[3]
							b.Cases(b.Term("I ⊆ T"))
							b.When(
								"I inside T: a subset of a finite set is finite and no larger",
								func(c *Argument, inside Fact) {
									c.Show(
										"I is finite with at most card(T) members",
										By(inside, finiteT, finite_set.FiniteSubset.At(I, T), cardinality.CardSubset.At(I, T)))
								})
							b.Otherwise(
								"a member v of I outside T replaces a member w of T outside I, one fewer outside",
								func(c *Argument, notInside Fact) {
									v, vOutsideT := c.ObtainAs[B](
										"I ⊄ T gives a member v of I outside T",
										"∃v:B. v ∈ I ∧ v ∉ T",
										BySets(notInside))
									w, exchange := c.ObtainAs[B](
										"the replacement step trades v for a member w of T outside I, the span still holding I",
										"∃w:B. w ∈ T ∧ w ∉ I ∧ I ⊆ module_span(R, M, insert(v, T ∖ {w}))",
										By(
											vOutsideT,
											scalarsField,
											tInM,
											independent,
											spannedByT,
											ReplacementStep.Read(moduleOn).At(inv, T, I, v)))
									traded := c.Conjuncts(
										exchange,
										"w lies in T",
										"w lies outside I",
										"the span of insert(v, T ∖ {w}) holds I")
									wInT, wOutsideI, spannedByNew := traded[0], traded[1], traded[2]

									rest, exchanged := c.TermAs[Set[B]]("T ∖ {w}"), c.TermAs[Set[B]]("insert(v, T ∖ {w})")
									finiteRest := c.Have(
										"T ∖ {w} is finite",
										"finite(T ∖ {w})",
										By(finiteT, finite_set.FiniteDiff.At(T, c.TermAs[Set[B]]("{w}"))))
									peel := c.Have(
										"w lies in T, so T is w laid into T ∖ {w}",
										"T = insert(w, T ∖ {w})",
										BySets(wInT))
									fresh := c.Have(
										"neither w nor v lies in T ∖ {w}",
										"w ∉ T ∖ {w} ∧ v ∉ T ∖ {w}",
										BySets(vOutsideT))
									sameSize := c.Have(
										"T and insert(v, T ∖ {w}) each have one member more than T ∖ {w}",
										"card(insert(v, T ∖ {w})) = card(T)",
										By(
											finiteRest,
											peel,
											fresh,
											cardinality.InsertCountsOneMore.At(rest, w),
											cardinality.InsertCountsOneMore.At(rest, v)))
									newInM := c.Have(
										"the exchanged set lies in M, v being a member of I",
										"insert(v, T ∖ {w}) ⊆ M.carrier",
										BySets(IndependentInCarrier.Read(independent), vOutsideT, tInM))
									fewerOutside := c.Have(
										"v lies in I and w, outside I, is gone: its members outside I are those of T but w",
										"insert(v, T ∖ {w}) ∖ I ⊊ T ∖ I",
										BySets(vOutsideT, wInT, wOutsideI))
									descends := c.Have(
										"so fewer of its members lie outside I",
										"card(insert(v, T ∖ {w}) ∖ I) < n",
										By(
											fewerOutside,
											finiteT,
											outsideT,
											cardinality.CardPsubset.At(c.TermAs[Set[B]]("insert(v, T ∖ {w}) ∖ I"), c.TermAs[Set[B]]("T ∖ I")),
											finite_set.FiniteDiff.At(T, I)))
									c.Show(
										"the bound at the exchanged set, of the same size as T",
										By(
											fewer.At(c.TermAs[Nat]("card(insert(v, T ∖ {w}) ∖ I)"), exchanged),
											descends,
											finiteRest,
											finite_set.FiniteInsert.At(v, rest),
											newInM,
											spannedByNew,
											sameSize))
								})
						}))))
		}),
})}
