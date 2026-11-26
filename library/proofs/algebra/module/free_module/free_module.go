// free_module.go — the free module on a set S over a commutative ring R:
// the finitely supported functions on S into R, finite_supp(R.zero,
// R.carrier, S), with R's operations read pointwise, which is
// function_module's finite_supp_module at R as a module over itself. Its
// generators are the indicators of the points of S, every member is the
// finite sum of its values scaling them, and they are a basis; a map of S
// into a module extends to one homomorphism, and the extension of the
// identity of a set spanning a module maps the free module on it onto the
// module, isomorphically when the set is a basis, so values prescribed on a
// basis extend linearly. A free module is projective: a linear map out of
// it lifts along any linear map whose image contains its own. A map of
// basis sets extends linearly to the pushforward between the free modules
// on them.

package free_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The free module
// ---------------------------------------------------------------------------

// FreeModuleRecordDef — `free_module_record(R, S)`: the free module on S
// over the ring R as a module record, its carrier finite_supp(R.zero,
// R.carrier, S) and its operations R's read pointwise.
var FreeModuleRecordDef = freeModuleRecordDefThm{family.Define(registry.DefEntry{
	Name: "FreeModuleRecordDef", Const: "free_module_record",
	Key:  "prop_e59d2dc7b6235001",
	Type: "ring_ops(A) → set(I) → module_ops(A, I → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(I). " +
			"    free_module_record(R, S) = " +
			"    mk_module(fun_add⟨D:I⟩(R.add), " +
			"        fun_zero⟨D:I⟩(R.zero), " +
			"        fun_neg⟨D:I⟩(R.neg), " +
			"        fun_smul⟨D:I⟩(R.mul), " +
			"        finite_supp(R.zero, R.carrier, S))",
	},
})}

// FreeModuleRecordFiniteSupp — the free module on S is the module of the
// finitely supported functions on S into R, R a module over itself: both
// records have the carrier finite_supp(R.zero, R.carrier, S) and R's
// operations read pointwise.
var FreeModuleRecordFiniteSupp = freeModuleRecordFiniteSuppThm{family.Add(registry.ProofEntry{
	Name: "FreeModuleRecordFiniteSupp",
	Key:  "prop_dae405b80c30a84e",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀S:set(D).",
		Conclusion: "free_module_record(R, S) = finite_supp_module(regular_module(R), S)",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]]) {
			a.Show(
				"both records unfold to R's operations read pointwise on finite_supp(R.zero, R.carrier, S)",
				Simp(Fwd(FreeModuleRecordDef), Fwd(function_module.FiniteSuppModuleDef)),
				Refl())
		}),
})}

// FreeModuleOn — the free module on S is a module over the commutative
// ring R: it is the module of finitely supported functions on S into the
// ring itself, and a commutative ring is a module over itself.
var FreeModuleOn = freeModuleOnThm{family.Add(registry.ProofEntry{
	Name: "FreeModuleOn",
	Key:  "prop_2b229923bc0540b3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "module_on(R, free_module_record(R, S))",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], ring Fact) {
			regular := a.Have(
				"R is a module over itself, its members the vectors and its product the scaling",
				"module_on(R, regular_module(R))",
				By(module.RegularModuleOn, ring))
			a.Show(
				"the free module on S is the module of the finitely supported "+
					"functions on S into R, and those into a module over R form one",
				Simp(Fwd(FreeModuleRecordFiniteSupp)),
				By(function_module.FiniteSuppModuleOn.Read(regular)))
		}),
})}

// CoordinateProjectionLinear — reading the functions of the free module on
// S at one index x is a linear functional on it, into R as a module over
// itself: both records are modules over the commutative ring R, a member
// takes its values in R's carrier, and the free module's sum and scaling
// are R's read pointwise, so at x they are R's sum and product of the
// values.
var CoordinateProjectionLinear = coordinateProjectionLinearThm{family.Add(registry.ProofEntry{
	Name: "CoordinateProjectionLinear",
	Key:  "prop_baefa2428ca9145b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "module_homomorphism(R, free_module_record(R, S), regular_module(R), λv:(D → A). v(x))",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], x *Expr[D], ring Fact) {
			free := a.Have(
				"the free module on S is a module over R",
				"module_on(R, free_module_record(R, S))",
				By(ring, FreeModuleOn.At(R, S)))
			regular := a.Have(
				"and so is R over itself",
				"module_on(R, regular_module(R))",
				By(ring, module.RegularModuleOn.At(R)))
			values := a.Have(
				"a member of the free module takes its values in R's carrier",
				"∀u:(D → A). u ∈ free_module_record(R, S).carrier ⇒ u(x) ∈ R.carrier",
				By(function_module.FiniteSuppMember))
			a.Show(
				"and the free module's sum and scaling, read at x, are R's sum and product of the values",
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				Simp(Fwd(function_module.FunAddDef), Fwd(function_module.FunSmulDef)),
				By(free, regular, values))
		}),
})}

// CoordinateRelation — a coordinate of a vanishing finite combination of a
// family of the free module vanishes: the free module's operations are R's
// read pointwise, so the sum evaluates at x term by term (ModuleSumApply, R
// a module over itself), to the combination of the x-coordinates with the
// same coefficients, and the zero vector to R's zero.
var CoordinateRelation = coordinateRelationThm{family.Add(registry.ProofEntry{
	Name: "CoordinateRelation",
	Key:  "prop_908f9a115b0a3c07",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(D). ∀T:set(E). ∀e:(E → D → A). ∀c:(E → A). ∀x:D.",
		Hypotheses: []string{
			"finite(T)",
			"(∀t:E. t ∈ T ⇒ e(t) ∈ free_module_record(R, S).carrier)",
			"(∀t:E. t ∈ T ⇒ c(t) ∈ R.carrier)",
			"module_sum(free_module_record(R, S).add, " +
				"    free_module_record(R, S).zero, " +
				"    T, " +
				"    λt:E. free_module_record(R, S).smul(c(t), e(t))) = " +
				"free_module_record(R, S).zero",
		},
		Conclusion: "module_sum(R.add, R.zero, T, λt:E. c(t) * e(t, x)) = R.zero",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[D]],
		T *Expr[Set[E]],
		e *Arrow2[E, D, A],
		c *Arrow[E, A],
		x *Expr[D],
		h Fact,
	) {
		opened := a.Simplified(h, Fwd(FreeModuleRecordDef), Fwd(function_module.FunSmulDef))
		regular := a.Have(
			"R is a module over itself",
			"module_on(R, regular_module(R))",
			By(R, module.RegularModuleOn))
		coordinates := a.Have(
			"a member of the free module takes its values in R's carrier",
			"∀u:(D → A). ∀y:D. u ∈ finite_supp(R.zero, R.carrier, S) ⇒ u(y) ∈ R.carrier",
			By(function_module.FiniteSuppMember))
		values := a.Have(
			"and so does each scaled summand",
			"∀t:E. ∀y:D. t ∈ T ⇒ c(t) * e(t, y) ∈ R.carrier",
			BySets(opened, coordinates, comm_ring.MulIn.Read(R)))
		combination := a.TermAs[Fun2[E, D, A]]("λt:E. λy:D. c(t) * e(t, y)")
		a.Show(
			"evaluated at x the sum is the combination of the coordinates, and the zero vector is R's zero",
			By(
				opened,
				values,
				function_module.ModuleSumApply.Read(regular).At(T, combination, x),
				function_module.FunZeroDef.At(a.TermAs[A]("R.zero"), x)))
	}),
})}

// ---------------------------------------------------------------------------
// Generators and the expansion
// ---------------------------------------------------------------------------

// DeltaAtDef — `delta_at(zero, one, x)`: the generator at x, one at x
// and zero elsewhere.
var DeltaAtDef = deltaAtDefThm{family.Define(registry.DefEntry{
	Name:      "DeltaAtDef",
	Key:       "prop_a922e6f69303d736",
	Const:     "delta_at",
	Type:      "A → A → D → D → A",
	Implicit:  []string{"zero", "one"},
	Equations: []string{"∀zero one:A. ∀x y:D. delta_at(zero, one, x, y) = COND(y = x, one, zero)"},
})}

// DeltaAtIn — the generator at a point x of S lies in the free module
// on S: it is zero away from x, so its support lies in the finite {x},
// which lies in S; and its values are the ring's one and zero, both in c.
var DeltaAtIn = deltaAtInThm{family.Add(registry.ProofEntry{
	Name: "DeltaAtIn",
	Key:  "prop_4d0030928f25a113",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(D). ∀x:D.",
		Hypotheses: []string{
			"x ∈ S",
		},
		Conclusion: "delta_at(x) ∈ finite_supp(R.zero, R.carrier, S)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], S *Expr[Set[D]], x *Expr[D], xIn Fact) {
			support, singleton :=
				a.TermAs[Set[D]]("fun_support(R.zero, λy:D. delta_at(x, y))"), a.TermAs[Set[D]]("{x}")
			zeroAwayFromX := a.Have(
				"away from x the generator is zero, so its support lies in {x}",
				"fun_support(R.zero, λy:D. delta_at(x, y)) ⊆ {x}",
				Simp(Fwd(DeltaAtDef)),
				BySets())
			finite := a.Have(
				"so its support is finite, lying in the finite {x}",
				"finite(fun_support(R.zero, λy:D. delta_at(x, y)))",
				By(zeroAwayFromX, finite_set.FiniteSubset.At(support, singleton), finite_set.FiniteSing.At(x)))
			inS := a.Have(
				"and lies in S, {x} lying in S",
				"fun_support(R.zero, λy:D. delta_at(x, y)) ⊆ S",
				By(
					zeroAwayFromX,
					xIn,
					set_order.SingSubset.At(S, x),
					set_order.SubsetTrans.At(support, singleton, S)))
			values := a.Have(
				"its values are one and zero, both in c",
				"∀y:D. delta_at(x, y) ∈ R.carrier",
				Simp(Fwd(DeltaAtDef)),
				By(comm_ring.ZeroIn.Read(ring), comm_ring.OneIn.Read(ring)))
			a.Show(
				"so it is a function of finite support inside S, valued in c",
				By(function_module.FiniteSuppMember, finite, inS, values))
		}),
})}

// DeltaAtCoefficientIn — the function r at a point x of S and zero
// elsewhere, r in the carrier, lies in the free module on S: its support
// lies in the finite {x}, which lies in S; and its values are r and the
// ring's zero, both in the carrier.
var DeltaAtCoefficientIn = deltaAtCoefficientInThm{family.Add(registry.ProofEntry{
	Name: "DeltaAtCoefficientIn",
	Key:  "prop_cac0818cef0deab1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀S:set(D). ∀r:A. ∀x:D.",
		Hypotheses: []string{"r ∈ R.carrier", "x ∈ S"},
		Conclusion: "delta_at(R.zero, r, x) ∈ finite_supp(R.zero, R.carrier, S)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			S *Expr[Set[D]],
			r *Expr[A],
			x *Expr[D],
			rIn, xIn Fact,
		) {
			support, singleton :=
				a.TermAs[Set[D]]("fun_support(R.zero, λy:D. delta_at(R.zero, r, x, y))"), a.TermAs[Set[D]]("{x}")
			zeroAwayFromX := a.Have(
				"away from x it is zero, so its support lies in {x}",
				"fun_support(R.zero, λy:D. delta_at(R.zero, r, x, y)) ⊆ {x}",
				Simp(Fwd(DeltaAtDef)),
				BySets())
			finite := a.Have(
				"so its support is finite, lying in the finite {x}",
				"finite(fun_support(R.zero, λy:D. delta_at(R.zero, r, x, y)))",
				By(zeroAwayFromX, finite_set.FiniteSubset.At(support, singleton), finite_set.FiniteSing.At(x)))
			inS := a.Have(
				"and lies in S, {x} lying in S",
				"fun_support(R.zero, λy:D. delta_at(R.zero, r, x, y)) ⊆ S",
				By(
					zeroAwayFromX,
					xIn,
					set_order.SingSubset.At(S, x),
					set_order.SubsetTrans.At(support, singleton, S)))
			values := a.Have(
				"its values are r and zero, both in the carrier",
				"∀y:D. delta_at(R.zero, r, x, y) ∈ R.carrier",
				Simp(Fwd(DeltaAtDef)),
				By(rIn, comm_ring.ZeroIn.Read(ring)))
			a.Show(
				"so it is a function of finite support inside S, valued in the carrier",
				By(function_module.FiniteSuppMember, finite, inS, values))
		}),
})}

// DeltaAtInjective — where one is not zero, the generators of two points
// differ unless the points agree: read at x, the generator at x is one, and
// the generator at y is zero away from y.
var DeltaAtInjective = deltaAtInjectiveThm{family.Add(registry.ProofEntry{
	Name: "DeltaAtInjective",
	Key:  "prop_585262ef337a971b",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{"R.one ≠ R.zero"},
		Conclusion: "injective_on(S, delta_at(R.zero, R.one))",
	}, func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], oneNotZero Fact) {
		a.Show(
			"two equal generators agree at x, where the first is one and the second zero unless x = y",
			Simp(Fwd(functions.InjectiveOnDef)),
			By(oneNotZero, DeltaAtDef))
	}),
})}

// HomDeltaIn — a homomorphism from the free module on S to the free
// module on T carries the generator at each point of S into the free
// module on T: the generator lies in the free module on S, R being a
// commutative ring since the source is a module over it, and a
// homomorphism maps its source's carrier into its target's.
var HomDeltaIn = homDeltaInThm{family.Add(registry.ProofEntry{
	Name: "HomDeltaIn",
	Key:  "prop_d07944fcbc1e0ed3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(I). ∀T:set(E). ∀k:((I → A) → E → A). ∀x:I.",
		Hypotheses: []string{
			"module_homomorphism(R, free_module_record(R, S), free_module_record(R, T), k)",
			"x ∈ S",
		},
		Conclusion: "k(delta_at(x)) ∈ finite_supp(R.zero, R.carrier, T)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[I]],
			T *Expr[Set[E]],
			k *Arrow[Fun[I, A], Fun[E, A]],
			x *Expr[I],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"k is a homomorphism of the free modules on S and T",
				"x is a point of S")
			linear, inS := parts[0], parts[1]
			ring := module.RingOn.Read(module_homomorphism.HomSource.Read(linear))
			a.Show(
				"the generator at x lies in the free module on S, which k carries into the free module on T",
				By(module_homomorphism.HomIn.Read(linear), DeltaAtIn.Read(ring), inS))
		}),
})}

// FreeModuleExpand — a member f of the free module is the sum, over its
// support, of its values scaling the generators. Two functions agree
// when they agree at every point y, and read at y the sum of the
// functions f(x) • δ_x is the sum of their values f(x) * δ_x(y) in the
// ring, a module over itself. Away from y a term is f(x) * zero = zero
// and at y it is f(y) * one = f(y): when y lies in the support that one
// term is the whole sum, and when it does not every term of the sum
// vanishes, as does f(y).
var FreeModuleExpand = freeModuleExpandThm{family.Add(registry.ProofEntry{
	Name: "FreeModuleExpand",
	Key:  "prop_7db7d6019d1579d5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(D). ∀f:(D → A).",
		Hypotheses: []string{
			"f ∈ finite_supp(R.zero, R.carrier, S)",
		},
		Conclusion: "f = " +
			"module_sum(fun_add⟨D:D⟩(R.add), " +
			"    fun_zero⟨D:D⟩(R.zero), " +
			"    fun_support(R.zero, f), " +
			"    λx:D. fun_smul(f(x), delta_at(x)))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], S *Expr[Set[D]], f *Arrow[D, A], member Fact) {
			regular := module.RegularModuleOn.Read(ring)
			parts := a.Conjuncts(
				a.Simplified(member, Fwd(function_module.FiniteSuppMember)),
				"the support of f is finite",
				"and lies in S",
				"f takes its values in c")
			finite, values := parts[0], parts[2]
			terms := a.Have(
				"each f(x) • δ_x takes its values in c, the ring's product of f(x) and one or zero",
				"∀x z:D. fun_smul(f(x), delta_at(x), z) ∈ R.carrier",
				Simp(Fwd(function_module.FunSmulDef), Fwd(DeltaAtDef)),
				By(values, comm_ring.MulIn.Read(ring), comm_ring.ZeroIn.Read(ring), comm_ring.OneIn.Read(ring)))

			a.Do(Funext())
			y := a.FixAs[D]("y")
			support := a.TermAs[Set[D]]("fun_support(R.zero, f)")
			scaled := a.TermAs[Fun2[D, D, A]]("λx:D. fun_smul(f(x), delta_at(x))")
			valueAtY := a.TermAs[Fun[D, A]]("λx:D. fun_smul(f(x), delta_at(x), y)")
			evaluate := a.Have(
				"read at y, the sum of the functions f(x) • δ_x is the sum of their values at y",
				"module_sum(fun_add⟨D:D⟩(R.add), "+
					"    fun_zero⟨D:D⟩(R.zero), "+
					"    fun_support(R.zero, f), "+
					"    λx:D. fun_smul(f(x), delta_at(x)), "+
					"    y) = "+
					"module_sum(R.add, R.zero, fun_support(R.zero, f), λx:D. fun_smul(f(x), delta_at(x), y))",
				By(finite, terms, function_module.ModuleSumApply.Read(regular).At(support, scaled, y)))
			a.Do(evaluate.Rw())
			away := a.Have(
				"away from y a term is f(x) * zero, which is zero",
				"∀x:D. x ≠ y ⇒ fun_smul(f(x), delta_at(x), y) = R.zero",
				Simp(Fwd(function_module.FunSmulDef), Fwd(DeltaAtDef)),
				a.ForEach(func(x *Expr[D]) Action {
					return By(values.At(x), comm_ring.MulRightZeroOn.Read(ring).AsFact().At(f.Apply(x)))
				}))
			atY := a.Have(
				"at y it is f(y) * one, which is f(y)",
				"fun_smul(f(y), delta_at(y), y) = f(y)",
				Simp(Fwd(function_module.FunSmulDef), Fwd(DeltaAtDef)),
				By(
					values.At(y),
					comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(f.Apply(y))))

			a.Cases(a.Term("f(y) = R.zero"))
			a.When(
				"when f(y) is zero, y is off the support and every term of the sum vanishes",
				func(b *Argument, vanishes Fact) {
					onSupport := b.Have(
						"a point of the support is not y, so its term vanishes",
						"∀x:D. x ∈ fun_support(R.zero, f) ⇒ fun_smul(f(x), delta_at(x), y) = R.zero",
						b.ForEach(func(x *Expr[D]) Action { return BySets(away.At(x), vanishes) }))
					b.Show(
						"a sum of zeros is zero, which is f(y)",
						By(finite, onSupport, vanishes, module.ModuleSumZero.Read(regular).At(support, valueAtY)))
				})
			a.Otherwise(
				"when f(y) is not zero, y lies in the support and its term is the only one left",
				func(b *Argument, nonzero Fact) {
					inSupport := b.Have(
						"y lies in the support of f",
						"y ∈ fun_support(R.zero, f)",
						BySets(nonzero))
					b.Show(
						"the sum is its term at y",
						By(
							finite,
							inSupport,
							terms,
							away,
							atY,
							module.ModuleSumSingle.Read(regular).At(support, y, valueAtY)))
				})
		}),
})}

// DeltaAtBasis — the delta functions at the points of S are a basis of
// the free module on S. They lie in it, and they span it: a member v is
// the finite sum, over its support, of its values scaling them
// (FreeModuleExpand), and the span is a submodule holding each term. They
// are independent: read at a point y of S, a combination of finitely
// many of them is the coefficient of the delta function at y, every
// other one vanishing at y, so a combination that vanishes has every
// coefficient R.zero.
var DeltaAtBasis = deltaAtBasisThm{family.Add(registry.ProofEntry{
	Name: "DeltaAtBasis",
	Key:  "prop_c2c9bedb95bce621",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀S:set(D).",
		Conclusion: "module_basis(R, free_module_record(R, S), image(delta_at, S))",
		Abbrev: Abbrev{
			{Name: "span", Text: "module_span(R, free_module_record(R, S), image(delta_at, S))"},
		},
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], S *Expr[Set[D]]) {
		regular := module.RegularModuleOn.Read(ring)
		R := a.TermAs[RingOps[A]]("R")
		free := a.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)")
		delta := a.TermAs[Fun2[D, D, A]]("delta_at")
		generators := a.TermAs[Set[Fun[D, A]]]("image(delta_at, S)")
		span := a.TermAs[Set[Fun[D, A]]]("«span»")
		freeCarrier := a.TermAs[Set[Fun[D, A]]]("free_module_record(R, S).carrier")
		zero, scalars := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
		freeOn := a.Have(
			"the free module on S is a module over R",
			"module_on(R, free_module_record(R, S))",
			By(ring, FreeModuleOn.At(R, S)))
		deltasIn := a.Have(
			"the delta functions at S lie in the free module",
			"image(delta_at, S) ⊆ free_module_record(R, S).carrier",
			BySets(At(DeltaAtIn.Read(ring), S)))
		supportData := a.Have(
			"a member has finite support in S and scalar values",
			Statement{
				Binders: "∀v:(D → A).",
				Hypotheses: []string{
					"v ∈ free_module_record(R, S).carrier",
				},
				Conclusion: "finite(fun_support(R.zero, v)) ∧ " +
					"fun_support(R.zero, v) ⊆ S ∧ " +
					"(∀x:D. v(x) ∈ R.carrier)",
			},
			Derive(func(b *Argument) {
				v := b.FixAs[Fun[D, A]]("v")
				inFree := b.Assume()
				b.Show(
					"the finite-support membership law gives these three properties",
					By(inFree, function_module.FiniteSuppMember.At(zero, scalars, S, v)))
			}))

		// The delta functions span the free module.
		spanSub := a.Have(
			"their span is a submodule",
			"submodule(R, free_module_record(R, S), «span»)",
			By(deltasIn, submodule.SpanSubmodule.Read(freeOn).At(generators)))
		covers := a.Have(
			"the delta functions span every member of the free module",
			"∀v:(D → A). v ∈ free_module_record(R, S).carrier ⇒ v ∈ «span»",
			Derive(func(b *Argument) {
				v := b.FixAs[Fun[D, A]]("v")
				inFree := b.Assume()
				data := b.Have(
					"v has finite support in S and scalar values",
					"finite(fun_support(R.zero, v)) ∧ fun_support(R.zero, v) ⊆ S ∧ (∀x:D. v(x) ∈ R.carrier)",
					By(supportData.At(v), inFree))
				parts := b.Conjuncts(
					data,
					"the support is finite",
					"the support lies in S",
					"the values are scalars")
				deltaInSpan := b.Have(
					"each delta function at S lies in the span",
					"∀x:D. x ∈ S ⇒ delta_at(x) ∈ «span»",
					Derive(func(c *Argument) {
						x := c.FixAs[D]("x")
						inS := c.Assume()
						inImage := c.Have(
							"the delta function at x is one of the generators",
							"delta_at(x) ∈ image(delta_at, S)",
							By(inS, set_image.FunInImage.At(delta, S, x)))
						c.Show(
							"a generator lies in its span",
							By(inImage, submodule.SubsetSpan.At(R, free, generators), set_basic.SubsetDef.At(generators, span)))
					}))
				termsIn := b.Have(
					"each supported value scaling its delta function lies in the span",
					"∀x:D. x ∈ fun_support(R.zero, v) ⇒ free_module_record(R, S).smul(v(x), delta_at(x)) ∈ «span»",
					Derive(func(c *Argument) {
						x := c.FixAs[D]("x")
						inSupport := c.Assume()
						inS := c.Have(
							"a supported point lies in S",
							"x ∈ S",
							BySets(inSupport, parts[1]))
						inSpan := c.Have(
							"its delta function lies in the span",
							"delta_at(x) ∈ «span»",
							By(inS, deltaInSpan.At(x)))
						c.Show(
							"the submodule is closed under scaling",
							By(parts[2].At(x), inSpan, submodule.SubmoduleSmul.Read(spanSub)))
					}))
				written := b.Have(
					"v is the sum of its supported values scaling the delta functions",
					"v = "+
						"module_sum(free_module_record(R, S).add, "+
						"    free_module_record(R, S).zero, "+
						"    fun_support(R.zero, v), "+
						"    λx:D. free_module_record(R, S).smul(v(x), delta_at(x)))",
					By(inFree, FreeModuleExpand.Read(ring).At(S, v)))
				sumIn := b.Have(
					"that finite sum lies in the span",
					"module_sum(free_module_record(R, S).add, "+
						"    free_module_record(R, S).zero, "+
						"    fun_support(R.zero, v), "+
						"    λx:D. free_module_record(R, S).smul(v(x), delta_at(x))) ∈ "+
						"«span»",
					By(
						parts[0],
						termsIn,
						spanSub,
						submodule.SubmoduleModuleSum.Read(freeOn).At(
							span,
							b.TermAs[Set[D]]("fun_support(R.zero, v)"),
							b.TermAs[Fun2[D, D, A]]("λx:D. free_module_record(R, S).smul(v(x), delta_at(x))"))))
				b.Show(
					"hence v lies in the span",
					By(Normalized, written, sumIn))
			}))
		covered := a.Have(
			"the free module lies in the span",
			"free_module_record(R, S).carrier ⊆ «span»",
			By(covers, set_basic.SubsetDef.At(freeCarrier, span)))
		within := a.Have(
			"the span lies in the free module",
			"«span» ⊆ free_module_record(R, S).carrier",
			By(submodule.SubmoduleSubset.Read(spanSub)))
		spans := a.Have(
			"so the delta functions span the free module",
			"«span» = free_module_record(R, S).carrier",
			By(covered, within, set_order.SubsetAntisym.At(span, freeCarrier)))

		// The delta functions are independent: a combination of them, read at
		// a point y of S, is the coefficient of the delta function at y.
		vanishing := a.Have(
			"a vanishing combination of finitely many delta functions has every coefficient R.zero",
			"∀T:set(D → A). ∀c:((D → A) → A). "+
				"    finite(T) ∧ "+
				"    T ⊆ image(delta_at, S) ∧ "+
				"    (∀w:(D → A). w ∈ T ⇒ c(w) ∈ R.carrier) ∧ "+
				"    module_sum(free_module_record(R, S).add, "+
				"        free_module_record(R, S).zero, "+
				"        T, "+
				"        λw:(D → A). free_module_record(R, S).smul(c(w), w)) = "+
				"    free_module_record(R, S).zero ⇒ "+
				"    ∀v:(D → A). v ∈ T ⇒ c(v) = R.zero",
			Derive(func(b *Argument) {
				T := b.FixAs[Set[Fun[D, A]]]("T")
				b.FixAs[Fun[Fun[D, A], A]]("c")
				given := b.Conjuncts(
					b.Assume(),
					"T is finite",
					"T consists of delta functions at S",
					"the coefficients are scalars",
					"the combination vanishes")
				finiteT, inGenerators, coefficients, vanishes := given[0], given[1], given[2], given[3]
				v := b.FixAs[Fun[D, A]]("v")
				vIn := b.Assume()
				vImage := b.Have(
					"v is a delta function at S",
					"v ∈ image(delta_at, S)",
					BySets(vIn, inGenerators))
				y, vAt := b.UnpackAs[D](b.Simplified(vImage, Fwd(set_basic.InImage)), "y")
				isDeltaY := b.Conjuncts(
					vAt,
					"v is the delta function at y",
					"y lies in S")[0]

				// Each term, read at any point, is a scalar.
				valuesT := b.Have(
					"a member of T lies in the free module, so its values are scalars",
					"∀w:(D → A). ∀z:D. w ∈ T ⇒ w(z) ∈ R.carrier",
					Derive(func(c *Argument) {
						w := c.FixAs[Fun[D, A]]("w")
						c.FixAs[D]("z")
						wIn := c.Assume()
						inFree := c.Have(
							"w lies in the free module",
							"w ∈ free_module_record(R, S).carrier",
							BySets(wIn, inGenerators, deltasIn))
						c.Show(
							"so its values are scalars",
							By(supportData.At(w), inFree))
					}))
				terms := b.Have(
					"each term c(w) • w of the combination takes scalar values",
					"∀w:(D → A). ∀z:D. w ∈ T ⇒ fun_smul⟨D:D⟩(R.mul, c(w), w, z) ∈ R.carrier",
					Simp(Fwd(function_module.FunSmulDef)),
					By(coefficients, valuesT, comm_ring.MulIn.Read(ring)))

				// Read at y, the combination is the sum in R of the values of its terms.
				combination := b.TermAs[Fun2[Fun[D, A], D, A]]("λw:(D → A). fun_smul⟨D:D⟩(R.mul, c(w), w)")
				valueAtY := b.TermAs[Fun[Fun[D, A], A]]("λw:(D → A). fun_smul⟨D:D⟩(R.mul, c(w), w, y)")
				evaluate := b.Have(
					"read at y, the combination is the sum in R of the values of its terms at y",
					"module_sum(free_module_record(R, S).add, "+
						"    free_module_record(R, S).zero, "+
						"    T, "+
						"    λw:(D → A). free_module_record(R, S).smul(c(w), w), "+
						"    y) = "+
						"module_sum(R.add, R.zero, T, λw:(D → A). fun_smul⟨D:D⟩(R.mul, c(w), w, y))",
					By(finiteT, terms, function_module.ModuleSumApply.Read(regular).At(T, combination, y)))
				zeroSum := b.Have(
					"so the sum of the values at y is R.zero, the combination vanishing",
					"module_sum(R.add, R.zero, T, λw:(D → A). fun_smul⟨D:D⟩(R.mul, c(w), w, y)) = R.zero",
					CalcEq(
						Leg(
							b.TermAs[A](
								"module_sum(free_module_record(R, S).add, "+
									"    free_module_record(R, S).zero, "+
									"    T, "+
									"    λw:(D → A). free_module_record(R, S).smul(c(w), w), "+
									"    y)"),
							"it is the combination read at y",
							By(evaluate)),
						Leg(
							b.TermAs[A]("free_module_record(R, S).zero(y)"),
							"the combination is the free module's zero",
							vanishes.Rw(),
							Basic()),
						FinalLeg(
							"which is R.zero at every point",
							Simp(Fwd(FreeModuleRecordDef), Fwd(module_record.ModZeroDef), Fwd(function_module.FunZeroDef)),
							Basic()),
					))

				// Only the term at v survives at y.
				others := b.Have(
					"every other term vanishes at y",
					"∀w:(D → A). w ∈ T ∧ w ≠ v ⇒ fun_smul⟨D:D⟩(R.mul, c(w), w, y) = R.zero",
					Derive(func(c *Argument) {
						w := c.FixAs[Fun[D, A]]("w")
						about := c.Conjuncts(
							c.Assume(),
							"w lies in T",
							"w is not v")
						wImage := c.Have(
							"w is a delta function at S",
							"w ∈ image(delta_at, S)",
							BySets(about[0], inGenerators))
						_, wAt := c.UnpackAs[D](c.Simplified(wImage, Fwd(set_basic.InImage)), "x")
						isDeltaX := c.Conjuncts(
							wAt,
							"w is the delta function at x",
							"x lies in S")[0]
						apart := c.Have(
							"x is not y, the delta function at y being v",
							"x ≠ y",
							By(about[1], isDeltaX, isDeltaY))
						vanishesAtY := c.Have(
							"so w vanishes at y",
							"w(y) = R.zero",
							isDeltaX.Rw(),
							Simp(Fwd(DeltaAtDef)),
							By(apart))
						c.Show(
							"and its term is c(w) * R.zero = R.zero",
							Simp(Fwd(function_module.FunSmulDef)),
							vanishesAtY.Rw(),
							By(about[0], coefficients.At(w), comm_ring.MulRightZeroOn.Read(ring)))
					}))
				oneAtY := b.Have(
					"v, the delta function at y, is R.one at y",
					"v(y) = R.one",
					isDeltaY.Rw(),
					Simp(Fwd(DeltaAtDef)),
					Basic())
				atV := b.Have(
					"so the term at v is c(v) * R.one = c(v)",
					"fun_smul⟨D:D⟩(R.mul, c(v), v, y) = c(v)",
					Simp(Fwd(function_module.FunSmulDef)),
					oneAtY.Rw(),
					By(
						vIn,
						coefficients.At(v),
						comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(
							b.TermAs[A]("c(v)"))))
				single := b.Have(
					"so the sum of the values at y is the term at v",
					"module_sum(R.add, R.zero, T, λw:(D → A). fun_smul⟨D:D⟩(R.mul, c(w), w, y)) = "+
						"fun_smul⟨D:D⟩(R.mul, c(v), v, y)",
					By(finiteT, vIn, terms, others, module.ModuleSumSingle.Read(regular).At(T, v, valueAtY)))
				b.Show(
					"c(v) is the term at v, the whole sum of the values at y, which is R.zero",
					CalcEq(
						Leg(
							b.TermAs[A]("fun_smul⟨D:D⟩(R.mul, c(v), v, y)"),
							"c(v) is the term at v",
							By(atV)),
						Leg(
							b.TermAs[A]("module_sum(R.add, R.zero, T, λw:(D → A). fun_smul⟨D:D⟩(R.mul, c(w), w, y))"),
							"which is the whole sum",
							By(single)),
						FinalLeg(
							"which vanishes",
							By(zeroSum)),
					))
			}))
		independent := a.Have(
			"so the delta functions are independent",
			"module_independent(R, free_module_record(R, S), image(delta_at, S))",
			By(deltasIn, vanishing, linear_independence.ModuleIndependentDef))
		a.Show(
			"independent and spanning, the delta functions are a basis of the free module",
			By(independent, spans, linear_independence.ModuleBasisDef))
	}),
})}

// FreeHomExpand — a homomorphism h out of the free module on S takes a
// member f to h(f) = Σ f(x) • h(δ_x), the sum over the support of f of the
// values of f scaling the images of the generators. Expand f in the
// generators, then carry the homomorphism through the finite sum and
// through each scaling; each term lies in the free module because the
// support of f lies in S, where the generators are members.
var FreeHomExpand = freeHomExpandThm{family.Add(registry.ProofEntry{
	Name: "FreeHomExpand",
	Key:  "prop_d9ae9d1e8e0220bc",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(D). ∀h:((D → A) → B). ∀f:(D → A).",
		Hypotheses: []string{
			"module_homomorphism(R, free_module_record(R, S), M, h)",
			"f ∈ finite_supp(R.zero, R.carrier, S)",
		},
		Conclusion: "h(f) = module_sum(M.add, M.zero, fun_support(R.zero, f), λx:D. f(x) • h(delta_at(x)))",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			S *Expr[Set[D]],
			h *Arrow[Fun[D, A], B],
			f *Arrow[D, A],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"h is linear on the free module on S",
				"f is a member of the free module on S")
			linear, member := hypotheses[0], hypotheses[1]
			ring := module.RingOn.Read(ambient)
			expand := a.Have(
				"f is the sum, over its support, of the f(x) • δ_x",
				"f = "+
					"module_sum(fun_add⟨D:D⟩(R.add), "+
					"    fun_zero⟨D:D⟩(R.zero), "+
					"    fun_support(R.zero, f), "+
					"    λx:D. fun_smul⟨D:D⟩(R.mul, f(x), delta_at(x)))",
				By(FreeModuleExpand.Read(ring).At(S, f), member))
			memberParts := a.Conjuncts(
				a.Simplified(member, Fwd(function_module.FiniteSuppMember)),
				"the support of f is finite",
				"it lies in S",
				"f takes its values in R")
			finite, inS, values := memberParts[0], memberParts[1], memberParts[2]
			terms := a.Have(
				"each f(x) • δ_x lies in the free module, δ_x being the generator at a point of S",
				Statement{
					Binders: "∀x:D.",
					Hypotheses: []string{
						"x ∈ fun_support(R.zero, f)",
					},
					Conclusion: "fun_smul⟨D:D⟩(R.mul, f(x), delta_at(x)) ∈ finite_supp(R.zero, R.carrier, S)",
				},
				By(
					module.SmulIn.Read(module_homomorphism.HomSource.Read(linear)),
					DeltaAtIn.Read(ring),
					inS,
					values,
					set_basic.SubsetDef))
			images := a.Have(
				"h carries f(x) • δ_x to f(x) • h(δ_x)",
				Statement{
					Binders: "∀x:D.",
					Hypotheses: []string{
						"x ∈ fun_support(R.zero, f)",
					},
					Conclusion: "h(fun_smul⟨D:D⟩(R.mul, f(x), delta_at(x))) = f(x) • h(delta_at(x))",
				},
				By(
					module_homomorphism.HomSmul.Read(linear),
					DeltaAtIn.Read(ring),
					inS,
					values,
					set_basic.SubsetDef))

			support := a.TermAs[Set[D]]("fun_support(R.zero, f)")
			a.Show(
				"so h(f) is the sum of the f(x) • h(δ_x)",
				CalcEq(
					// f occurs inside its own expansion, at every f(x), so the
					// leg rewrites the expansion back to f, not f forward; the
					// two sides then agree.
					Leg(
						a.TermAs[B](
							"h(module_sum(fun_add⟨D:D⟩(R.add), "+
								"        fun_zero⟨D:D⟩(R.zero), "+
								"        fun_support(R.zero, f), "+
								"        λx:D. fun_smul⟨D:D⟩(R.mul, f(x), delta_at(x))))"),
						"f is the sum of the f(x) • δ_x",
						expand.RwRev(),
						Basic()),
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    fun_support(R.zero, f), "+
								"    λx:D. h(fun_smul⟨D:D⟩(R.mul, f(x), delta_at(x))))"),
						"h, being linear, carries the finite sum to the sum of the images of its terms",
						By(
							module_homomorphism.HomSum.Read(linear).At(
								support, a.TermAs[Fun[D, Fun[D, A]]]("λx:D. fun_smul⟨D:D⟩(R.mul, f(x), delta_at(x))")),
							terms,
							finite)),
					FinalLeg(
						"and each image is f(x) • h(δ_x)",
						By(module.ModuleSumCongruence, images)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The universal property
// ---------------------------------------------------------------------------

// FreeLiftDef — `free_lift(zero, add, zero', smul, phi, f)`: the map phi
// of a set into a module extended to the free module, f ↦ Σ f(x) •
// phi(x) over the support, zero the ring's zero and add, zero', smul the
// module's sum, zero and scaling. Into a module M over a ring R it is
// `free_lift(R.zero, M.add, M.zero, M.smul, phi)`.
var FreeLiftDef = freeLiftDefThm{family.Define(registry.DefEntry{
	Name:  "FreeLiftDef",
	Key:   "prop_7e9820b532d389a9",
	Const: "free_lift",
	Type:  "A → (B → B → B) → B → (A → B → B) → (D → B) → (D → A) → B",
	Equations: []string{
		"∀zero:A. ∀add:(B → B → B). ∀zero':B. ∀smul:(A → B → B). ∀phi:(D → B). ∀f:(D → A). " +
			"    free_lift(zero, add, zero', smul, phi, f) = " +
			"    module_sum(add, zero', fun_support(zero, f), λx:D. smul(f(x), phi(x)))",
	},
})}

// FreeLiftHom — a map phi of S into M's carrier extends to a
// homomorphism from the free module on S into M. At a point x of S,
// scaling phi(x) is a homomorphism of R, a module over itself, into M:
// it is additive in the scalar and commutes with scaling. The free
// module on S is the module of the finitely supported functions on S
// into R, and homomorphisms out of R, one at each point of S, sum to a
// homomorphism out of it, g ↦ Σ g(x) • phi(x) over the support of g,
// which is the extension.
var FreeLiftHom = freeLiftHomThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftHom",
	Key:  "prop_69e1f0f7d7a80c89",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(D). ∀phi:(D → B).",
		Hypotheses: []string{
			"∀x:D. x ∈ S ⇒ phi(x) ∈ M.carrier",
		},
		Conclusion: "module_homomorphism(R, " +
			"    free_module_record(R, S), " +
			"    M, " +
			"    free_lift(R.zero, M.add, M.zero, M.smul, phi))",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			S *Expr[Set[D]],
			phi *Arrow[D, B],
			phiIn Fact,
		) {
			R, M, scalars :=
				a.TermAs[RingOps[A]]("R"),
				a.TermAs[ModuleOps[A, B]]("M"),
				a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			regular := a.Have(
				"R is a module over itself, its members the vectors and its product the scaling",
				"module_on(R, regular_module(R))",
				By(module.RegularModuleOn, module.RingOn.Read(ambient)))
			scalings := a.Have(
				"at a point x of S, scaling phi(x) is a homomorphism of R "+
					"into M, additive in the scalar and commuting with scaling",
				"∀x:D. x ∈ S ⇒ module_homomorphism(R, regular_module(R), M, λc:A. c • phi(x))",
				a.ForEach(func(x *Expr[D]) Action {
					return By(
						phiIn.At(x),
						regular,
						ambient,
						module.SmulIn.Read(ambient),
						module.SmulAddRight.Read(ambient),
						module.SmulMul.Read(ambient),
						module_homomorphism.ModuleHomomorphismDef)
				}))
			extension := a.Have(
				"the extension is the map g ↦ Σ g(x) • phi(x) over the support of g",
				"free_lift(R.zero, M.add, M.zero, M.smul, phi) = "+
					"(λg:(D → A). module_sum(M.add, M.zero, fun_support(R.zero, g), λx:D. g(x) • phi(x)))",
				Cite(FreeLiftDef))
			a.Show(
				"the free module on S is the module of the finitely supported "+
					"functions on S into R, and the scalings sum to a homomorphism out of it",
				extension.Rw(),
				Simp(Fwd(FreeModuleRecordFiniteSupp)),
				By(
					function_module.FiniteSuppSumHom.At(
						R, scalars, M, S, a.TermAs[Fun2[D, A, B]]("λx:D. λc:A. c • phi(x)")),
					regular,
					ambient,
					scalings))
		}),
})}

// FreeLiftDelta — the extension of phi takes the generator at a point x
// of S to phi(x). The generator vanishes away from x, so its support lies
// in {x}, and the sum defining the extension may run over {x} instead: if
// x lies outside the support its term is R.zero • phi(x) = M.zero. Over
// {x} the sum is its one term, δ_x(x) • phi(x) = R.one • phi(x) = phi(x).
var FreeLiftDelta = freeLiftDeltaThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftDelta",
	Key:  "prop_3d5f43e41ba2862b",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(D). ∀phi:(D → B). ∀x:D.",
		Hypotheses: []string{
			"∀y:D. y ∈ S ⇒ phi(y) ∈ M.carrier",
			"x ∈ S",
		},
		Conclusion: "free_lift(R.zero, M.add, M.zero, M.smul, phi, delta_at(x)) = phi(x)",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			S *Expr[Set[D]],
			phi *Arrow[D, B],
			x *Expr[D],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"phi carries S into M",
				"x is a point of S")
			phiX := a.MemberOf[on.M](phi.Apply(x), a.Have(
				"so phi(x) lies in M",
				"phi(x) ∈ M.carrier",
				By(parts[0].At(x), parts[1])))
			ring := module.RingOn.Read(ambient)

			// The generator is R.one at x and R.zero away from it.
			atX := a.Have(
				"the generator is R.one at x",
				"delta_at(x, x) = R.one",
				Simp(Fwd(DeltaAtDef)),
				Basic())
			inside := a.Have(
				"away from x it is R.zero, so its support lies in {x}",
				"fun_support(R.zero, λy:D. delta_at(x, y)) ⊆ {x}",
				Simp(Fwd(DeltaAtDef)),
				BySets())

			// The terms δ_x(y) • phi(y) of the extension's sum, read over {x}.
			single, support :=
				a.TermAs[Set[D]]("{x}"), a.TermAs[Set[D]]("fun_support(R.zero, λy:D. delta_at(x, y))")
			terms := a.TermAs[Fun[D, B]]("λy:D. delta_at(x, y) • phi(y)")
			inM := a.Have(
				"over {x} the one term is R.one • phi(x), which lies in M",
				"∀y:D. y ∈ {x} ⇒ delta_at(x, y) • phi(y) ∈ M.carrier",
				Derive(func(b *Argument) {
					b.FixAs[D]("y")
					yIn := b.Assume()
					isX := b.Have(
						"y is x, the one index of {x}",
						"y = x",
						By(yIn, set_basic.InSing))
					b.Show(
						"so its term R.one • phi(x) scales a vector of M by a scalar",
						isX.Rw(),
						atX.Rw(),
						By(phiX, comm_ring.OneIn.Read(ring), module.SmulIn.Read(ambient)))
				}))
			offSupport := a.Have(
				"if x lies outside the support, its term is R.zero • phi(x) = M.zero",
				"∀y:D. y ∈ {x} ∧ y ∉ fun_support(R.zero, λy:D. delta_at(x, y)) ⇒ delta_at(x, y) • phi(y) = M.zero",
				Derive(func(b *Argument) {
					b.FixAs[D]("y")
					where := b.Conjuncts(
						b.Assume(),
						"y lies in {x}",
						"outside the support of the generator")
					zero := b.Have(
						"the generator vanishes at y",
						"delta_at(x, y) = R.zero",
						BySets(where[1]))
					isX := b.Have(
						"and y is x",
						"y = x",
						By(where[0], set_basic.InSing))
					b.Show(
						"R.zero scales phi(x) to M.zero",
						zero.Rw(),
						isX.Rw(),
						By(module.ZeroSmul.Read(ambient).At(phiX)))
				}))
			xIn := a.Have(
				"x is an index of {x}",
				"x ∈ {x}",
				By(set_basic.InSing.At(x, x)))
			alone := a.Have(
				"and the only one",
				"∀y:D. y ∈ {x} ∧ y ≠ x ⇒ delta_at(x, y) • phi(y) = M.zero",
				BySets())

			a.Show(
				"so the extension at the generator is phi(x)",
				CalcEq(
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    fun_support(R.zero, λy:D. delta_at(x, y)), "+
								"    λy:D. delta_at(x, y) • phi(y))"),
						"the extension sums δ_x(y) • phi(y) over the support of the generator",
						Cite(FreeLiftDef)),
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, {x}, λy:D. delta_at(x, y) • phi(y))"),
						"the support lies in the finite set {x}, and the term "+
							"at x vanishes off it, so the sum may run over {x}",
						By(
							finite_set.FiniteSing.At(x),
							inside,
							inM,
							offSupport,
							module.ModuleSumSupport.Read(ambient).At(single, support, terms))),
					Leg(
						a.TermAs[B]("delta_at(x, x) • phi(x)"),
						"a sum over {x} is its term at x",
						By(
							finite_set.FiniteSing.At(x),
							xIn,
							inM,
							alone,
							module.ModuleSumSingle.Read(ambient).At(single, x, terms))),
					FinalLeg(
						"the generator is R.one at x, and R.one fixes phi(x)",
						atX.Rw(),
						By(module.SmulOne.Read(ambient).At(phiX))),
				))
		}),
})}

// FreeLiftOver — the extension of phi at a function f supported in a finite
// set T is the sum over T of f(x) • phi(x): it is the sum over the support of
// f, and on T off that support each term is R.zero • phi(x) = M.zero.
var FreeLiftOver = freeLiftOverThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftOver",
	Key:  "prop_38028e0ba7370927",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀T:set(D). ∀phi:(D → B). ∀f:(D → A).",
		Hypotheses: []string{
			"finite(T)",
			"fun_support(R.zero, f) ⊆ T",
			"∀x:D. x ∈ T ⇒ f(x) ∈ R.carrier",
			"∀x:D. x ∈ T ⇒ phi(x) ∈ M.carrier",
		},
		Conclusion: "free_lift(R.zero, M.add, M.zero, M.smul, phi, f) = " +
			"module_sum(M.add, M.zero, T, λx:D. f(x) • phi(x))",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			T *Expr[Set[D]],
			phi *Arrow[D, B],
			f *Arrow[D, A],
			finite, support, fIn, phiIn Fact,
		) {
			terms := a.TermAs[Fun[D, B]]("λx:D. f(x) • phi(x)")
			inM := a.Have(
				"on T each term lies in M",
				"∀x:D. x ∈ T ⇒ f(x) • phi(x) ∈ M.carrier",
				By(fIn, phiIn, module.SmulIn.Read(ambient)))
			offSupport := a.Have(
				"on T off the support of f each term is R.zero • phi(x) = M.zero",
				"∀x:D. x ∈ T ∧ x ∉ fun_support(R.zero, f) ⇒ f(x) • phi(x) = M.zero",
				By(Normalized, phiIn, module.ZeroSmul.Read(ambient)))
			a.Show(
				"the sum over the support of f is the sum over T",
				Simp(Fwd(FreeLiftDef)),
				By(
					finite,
					support,
					inM,
					offSupport,
					module.ModuleSumSupport.Read(ambient).At(T, a.TermAs[Set[D]]("fun_support(R.zero, f)"), terms)))
		}),
})}

// FreeLiftUnique — two homomorphisms out of the free module that agree
// on the generators of S agree on the free module: the uniqueness half of
// the free module's universal property, the homomorphism FreeLiftHom builds
// being the only one taking each δ_x to phi(x). At a member f each is the
// sum, over the support of f, of the f(x) scaling its values on the
// generators; the support lies in S, where those values agree, so the two
// sums agree term by term.
var FreeLiftUnique = freeLiftUniqueThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftUnique",
	Key:  "prop_d2a29bfff0310526",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(D). ∀g h:((D → A) → B). ∀f:(D → A).",
		Hypotheses: []string{
			"module_homomorphism(R, free_module_record(R, S), M, g)",
			"module_homomorphism(R, free_module_record(R, S), M, h)",
			"∀x:D. x ∈ S ⇒ g(delta_at(x)) = h(delta_at(x))",
			"f ∈ finite_supp(R.zero, R.carrier, S)",
		},
		Conclusion: "g(f) = h(f)",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			S *Expr[Set[D]],
			g, h *Arrow[Fun[D, A], B],
			f *Arrow[D, A],
			linearG, linearH, agree, member Fact,
		) {
			termwise := a.Have(
				"the support of f lies in S, where g and h agree on "+
					"the generators, so the terms of the two sums agree",
				"∀x:D. x ∈ fun_support(R.zero, f) ⇒ f(x) • g(delta_at(x)) = f(x) • h(delta_at(x))",
				By(agree, member, function_module.FiniteSuppMember, set_basic.SubsetDef))
			a.Show(
				"g(f) and h(f) are the same sum over the support of f",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, fun_support(R.zero, f), λx:D. f(x) • g(delta_at(x)))"),
						"g(f) is the sum of the f(x) • g(δ_x)",
						By(FreeHomExpand.Read(ambient).At(S, g, f), linearG, member)),
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, fun_support(R.zero, f), λx:D. f(x) • h(delta_at(x)))"),
						"the two sums agree term by term",
						By(module.ModuleSumCongruence, termwise)),
					FinalLeg(
						"and the sum of the f(x) • h(δ_x) is h(f)",
						By(FreeHomExpand.Read(ambient).At(S, h, f), linearH, member)),
				))
		}),
})}

// FreeLiftMapLinear — the extension free_lift is linear in the map it
// extends.
var FreeLiftMapLinear = freeLiftMapLinearThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftMapLinear",
	Key:  "prop_dfc74913c158faa4",
	Reading: "FreeLiftHom is linearity in f, this in the other argument: " +
		"free_lift is the bilinear pairing of the free module on S with the M-valued " +
		"functions on S. φ and ψ are read only on S, where the support of f lies.",
	Deps: []registry.EntryLike{
		FreeLiftDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		module.RingOn,
		module.SmulIn,
		module.SmulAddRight,
		module.SmulMul,
		module.SmulZero,
		module.ModuleSumCongruence,
		module.ModuleSumAdd,
		module.ModuleSumSmul,
		module.ModuleSumZero,
		comm_ring.MulMonoidOn,
		comm_monoid.CommOn,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀S:set(D). ∀f:(D → A). ∀φ ψ:(D → B). ∀c:A.",
		Hypotheses: []string{
			"f ∈ finite_supp(R.zero, R.carrier, S)",
			"∀x:D. x ∈ S ⇒ φ(x) ∈ M.carrier ∧ ψ(x) ∈ M.carrier",
			"c ∈ R.carrier",
		},
		Conclusion: "free_lift(R.zero, M.add, M.zero, M.smul, λx:D. M.add(φ(x), ψ(x)), f) = " +
			"M.add(free_lift(R.zero, M.add, M.zero, M.smul, φ, f), " +
			"    free_lift(R.zero, M.add, M.zero, M.smul, ψ, f)) ∧ " +
			"free_lift(R.zero, M.add, M.zero, M.smul, λx:D. M.smul(c, φ(x)), f) = " +
			"M.smul(c, free_lift(R.zero, M.add, M.zero, M.smul, φ, f)) ∧ " +
			"free_lift(R.zero, M.add, M.zero, M.smul, λx:D. M.zero, f) = M.zero",
	}),
		"free_lift is the finite sum over the support of f, which lies inside S (FreeLiftDef, "+
			"FiniteSuppDef, FiniteSupportDef), each term in M's carrier (SmulIn). Termwise f(x) • (φ(x) + "+
			"ψ(x)) = f(x) • φ(x) + f(x) • ψ(x) (SmulAddRight), and the sum splits (ModuleSumCongruence, "+
			"ModuleSumAdd); f(x) • (c • φ(x)) = (f(x) * c) • φ(x) = c • (f(x) • φ(x)) by SmulMul and the "+
			"ring being commutative (RingOn, MulMonoidOn, CommOn), and ModuleSumSmul takes c out; f(x) • "+
			"M.zero = M.zero (SmulZero), and a sum of zeros is M.zero (ModuleSumZero)"),
})}

// FreeLiftOntoSpanning — a module is the image of the free module on any
// set E spanning it: the extension of the identity of E carries the free
// module on E onto M, so a finitely generated module is the image of a
// free module on finitely many generators. The extension is linear
// (FreeLiftHom) and takes the delta function at a point of E to that
// point (FreeLiftDelta); a homomorphism carries the span of a set onto
// the span of its image, and the delta functions at E span the free
// module (DeltaAtBasis), so the image is the span of E, which is M.
var FreeLiftOntoSpanning = freeLiftOntoSpanningThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftOntoSpanning",
	Key:  "prop_e816cc8468b32350",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B).",
		Hypotheses: []string{
			"E ⊆ M.carrier",
			"module_span(R, M, E) = M.carrier",
		},
		Conclusion: "image(free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u), " +
			"    finite_supp(R.zero, R.carrier, E)) = " +
			"M.carrier",
	}, func(a *Argument, ambient module.ModuleFact[on.R, on.M], E *Expr[Set[B]], given Fact) {
		parts := a.Conjuncts(
			given,
			"E lies in M",
			"E spans M")
		eInM, spansM := parts[0], parts[1]
		ring := module.RingOn.Read(ambient)
		R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
		free := a.TermAs[ModuleOps[A, Fun[B, A]]]("free_module_record(R, E)")
		generators := a.TermAs[Set[Fun[B, A]]]("image(delta_at, E)")
		identity := a.TermAs[Fun[B, B]]("λu:B. u")
		lift := a.TermAs[Fun[Fun[B, A], B]]("free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u)")
		basis := a.Have(
			"the delta functions at E are a basis of the free module on E",
			"module_basis(R, free_module_record(R, E), image(delta_at, E))",
			By(DeltaAtBasis.Read(ring).At(E)))
		ofBasis := a.Conjuncts(
			a.Unfolded(basis, linear_independence.ModuleBasisDef),
			"the delta functions at E are independent",
			"and span the free module on E")
		deltasIn := a.Have(
			"they lie in the free module on E",
			"image(delta_at, E) ⊆ free_module_record(R, E).carrier",
			By(linear_independence.IndependentInCarrier.Read(ofBasis[0])))
		eachE := a.Unfolded(eInM, set_basic.SubsetDef)
		linear := a.Have(
			"the extension of the identity of E is a homomorphism of the free module on E into M",
			"module_homomorphism(R, "+
				"    free_module_record(R, E), "+
				"    M, "+
				"    free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u))",
			By(eachE, FreeLiftHom.Read(ambient).At(E, identity)))
		onDeltas := a.Have(
			"it takes the delta function at a point of E to that point",
			"∀x:B. x ∈ E ⇒ free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u, delta_at(x)) = x",
			By(eachE, At(FreeLiftDelta.Read(ambient), E, identity)))
		images := a.Have(
			"so it carries the delta functions at E onto E",
			"image(free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u), image(delta_at, E)) = E",
			BySets(onDeltas))
		a.Show(
			"it carries their span, the free module on E, onto the span of E, which is M",
			By(
				linear,
				deltasIn,
				ofBasis[1],
				images,
				spansM,
				linear_independence.HomSpan.At(R, free, M, lift, generators)))
	}),
})}

// FreeLiftOnto — every module is a quotient of a free module: the
// extension of the identity, from the free module on M's own carrier,
// maps onto that carrier. The carrier is a submodule, so it spans itself,
// and the image of the free module on a spanning set is all of M.
var FreeLiftOnto = freeLiftOntoThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftOnto",
	Key:  "prop_34ab8fd0b46b813f",
	Build: module.ModuleOn.Law("image(free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u), "+
		"    finite_supp(R.zero, R.carrier, M.carrier)) = "+
		"M.carrier",
		func(a *Argument, ambient module.ModuleFact[on.R, on.M]) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			carrier := a.TermAs[Set[B]]("M.carrier")
			spans := a.Have(
				"the carrier is a submodule, so it spans itself",
				"module_span(R, M, M.carrier) = M.carrier",
				By(submodule.CarrierSubmodule.Read(ambient), submodule.SpanOfSubmodule.At(R, M, carrier)))
			a.Show(
				"the carrier lies in itself and spans M, so the free module on it maps onto M",
				By(spans, set_order.SubsetRefl.At(carrier), FreeLiftOntoSpanning.Read(ambient).At(carrier)))
		}),
})}

// BasisFreeLiftIsomorphism — a module with basis E is isomorphic to the
// free module on E by extending the identity: independence kills the
// coefficients of a kernel element over its finite support, and spanning
// makes the extension onto.
var BasisFreeLiftIsomorphism = basisFreeLiftIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "BasisFreeLiftIsomorphism",
	Key:  "prop_df8534927b8a08ab",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B).",
		Hypotheses: []string{
			"module_basis(R, M, E)",
		},
		Conclusion: "module_isomorphism(R, free_module_record(R, E), M, «identityLift»)",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], E *Expr[Set[B]], basis Fact) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			basisFacts := a.Have(
				"E is independent, spans M, and lies in M",
				"module_independent(R, M, E) ∧ module_span(R, M, E) = M.carrier ∧ E ⊆ M.carrier",
				By(basis, linear_independence.ModuleBasisDef, linear_independence.BasisInCarrier))
			linear := a.Have(
				"the extension of the identity of E is linear",
				"module_homomorphism(R, free_module_record(R, E), M, «identityLift»)",
				By(ambient, basisFacts, FreeLiftHom, set_basic.SubsetDef))
			zeroCoefficients := a.Have(
				"a coefficient function in the kernel vanishes",
				Statement{
					Binders: "∀c:(B → A).",
					Hypotheses: []string{
						"c ∈ free_module_record(R, E).carrier",
						"«identityLift»(c) = M.zero",
					},
					Conclusion: "c = fun_zero(R.zero)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[Fun[B, A]]("c")
					given := b.Assume()
					s, support := b.LetAs[Set[B]]("s", "fun_support(R.zero, c)")
					supported := b.Have(
						"the support is a finite part of E and every coefficient lies in R",
						"finite(s) ∧ s ⊆ E ∧ (∀x:B. c(x) ∈ R.carrier)",
						By(
							support,
							given,
							function_module.FiniteSuppMember.At(b.TermAs[A]("R.zero"), b.TermAs[Set[A]]("R.carrier"), E, c)))
					vanishing := b.Have(
						"the lift is the vanishing combination over this support",
						"module_sum(M.add, M.zero, s, λx:B. M.smul(c(x), x)) = M.zero",
						By(
							support,
							given,
							FreeLiftDef.At(
								b.TermAs[A]("R.zero"),
								b.TermAs[Op[B]]("M.add"),
								b.TermAs[B]("M.zero"),
								b.TermAs[Fun2[A, B, B]]("M.smul"),
								b.TermAs[Fun[B, B]]("λu:B. u"),
								c)))
					onSupport := b.Have(
						"independence forces every supported coefficient to vanish",
						"∀x:B. x ∈ s ⇒ c(x) = R.zero",
						By(
							vanishing,
							supported,
							basisFacts,
							At(linear_independence.IndependentVanishingCombination, R, M, E, s, c)))
					b.Show(
						"off its support c vanishes by definition, so c is the zero function",
						BySets(onSupport, support, function_module.FunZeroDef))
				}))
			kernel := a.Have(
				"the kernel contains precisely the free module's zero",
				"group_kernel(M.zero, free_module_record(R, E).carrier, «identityLift») = "+
					"{free_module_record(R, E).zero}",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					v := b.FixAs[Fun[B, A]]("v")
					b.Show(
						"a kernel element is zero, and linearity places zero in the kernel",
						BySets(
							group.OneIn.Read(module.AddGroupOn.Read(module_homomorphism.HomSource.Read(linear))),
							module_homomorphism.HomZero.Read(linear),
							zeroCoefficients.At(v),
							group_homomorphism.GroupKernelDef.At(
								b.TermAs[B]("M.zero"),
								b.TermAs[Set[Fun[B, A]]]("free_module_record(R, E).carrier"),
								b.TermAs[Fun[Fun[B, A], B]]("«identityLift»"))))
				}))
			injective := a.Have(
				"the trivial kernel makes the linear lift injective",
				"injective_on(free_module_record(R, E).carrier, «identityLift»)",
				By(module_homomorphism.KernelTrivialIffInjective.Read(linear), kernel))
			onto := a.Have(
				"spanning makes the free lift surjective",
				"image(«identityLift», free_module_record(R, E).carrier) = M.carrier",
				By(basisFacts, FreeLiftOntoSpanning.Read(ambient).At(E)))
			free := a.TermAs[ModuleOps[A, Fun[B, A]]]("free_module_record(R, E)")
			lift := a.TermAs[Fun[Fun[B, A], B]]("«identityLift»")
			a.Show(
				"the lift is a linear bijection of the module carriers",
				By(linear, injective, onto, module_homomorphism.ModuleIsomorphismDef.At(R, free, M, lift)))
		}),
})}

// BasisLinearExtension — prescribed values on any basis extend to a
// linear map: use the inverse basis lift for coordinates, then apply the
// free lift of those values. A basis element has its delta function as
// coordinates, so the composite takes the prescribed value there.
var BasisLinearExtension = basisLinearExtensionThm{family.Add(registry.ProofEntry{
	Name: "BasisLinearExtension",
	Key:  "prop_eb4cdbb687f1b07f",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:module_ops(A, C). ∀E:set(B). ∀φ:(B → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_basis(R, M, E)",
			"∀e:B. e ∈ E ⇒ φ(e) ∈ N.carrier",
		},
		Conclusion: "∃f:(B → C). module_homomorphism(R, M, N, f) ∧ (∀e:B. e ∈ E ⇒ f(e) = φ(e))",
		Abbrev: Abbrev{
			{Name: "inverseLift", Text: "inverse_on(free_module_record(R, E).carrier, «identityLift»)"},
			{Name: "valueLift", Text: "free_lift(R.zero, N.add, N.zero, N.smul, φ)"},
			{Name: "extension", Text: "«valueLift» ∘ «inverseLift»"},
		},
	},
		func(
			a *Argument,
			source module.ModuleFact[on.R, on.M],
			N *Expr[ModuleOps[A, C]],
			E *Expr[Set[B]],
			φ *Arrow[B, C],
			target module.ModuleFact[on.R, on.N],
			basis, values Fact,
		) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			ring := module.RingOn.Read(source)
			free := a.TermAs[ModuleOps[A, Fun[B, A]]]("free_module_record(R, E)")
			lift := a.TermAs[Fun[Fun[B, A], B]]("«identityLift»")
			inverse := a.TermAs[Fun[B, Fun[B, A]]]("«inverseLift»")
			valueLift := a.TermAs[Fun[Fun[B, A], C]]("«valueLift»")
			eachBasis := a.Have(
				"every basis element lies in M",
				"∀e:B. e ∈ E ⇒ e ∈ M.carrier",
				By(basis, linear_independence.BasisInCarrier, set_basic.SubsetDef))
			basisIso := a.Have(
				"the identity lift identifies the free module on E with M",
				"module_isomorphism(R, free_module_record(R, E), M, «identityLift»)",
				By(basis, BasisFreeLiftIsomorphism.Read(source).At(E)))
			coordinates := a.Have(
				"the inverse lift is linear and the forward lift is injective",
				"module_homomorphism(R, M, free_module_record(R, E), «inverseLift») ∧ "+
					"injective_on(free_module_record(R, E).carrier, «identityLift»)",
				By(
					module_homomorphism.IsomorphismInverse.Read(basisIso),
					module_homomorphism.ModuleIsomorphismDef.At(R, M, free, inverse),
					module_homomorphism.ModuleIsomorphismDef.At(R, free, M, lift)))
			liftedValues := a.Have(
				"the prescribed basis values extend linearly out of the free module",
				"module_homomorphism(R, free_module_record(R, E), N, «valueLift»)",
				By(values, FreeLiftHom.Read(target)))
			a.Take(a.TermAs[Fun[B, C]]("«extension»"))
			a.Show(
				"the composite is linear and takes the prescribed values on E",
				SplitConj(
					Case(
						"the composite of the two linear maps is linear",
						By(
							coordinates,
							liftedValues,
							module_homomorphism.HomCompose.At(R, M, free, N, inverse, valueLift))),
					Case(
						"the composite takes the prescribed value on E",
						Derive(func(b *Argument) {
							e := b.FixAs[B]("e")
							eIn := b.Assume()
							δ, generator := b.LetAs[Fun[B, A]]("δ", "delta_at(e)")
							inFree := b.Have(
								"the delta function lies in the free module on E",
								"δ ∈ free_module_record(R, E).carrier",
								By(Normalized, generator, eIn, DeltaAtIn.Read(ring).At(E, e)))
							identityValue := b.Have(
								"the identity lift sends this generator to e",
								"«identityLift»(δ) = e",
								By(
									Normalized,
									eachBasis,
									generator,
									eIn,
									FreeLiftDelta.Read(source).At(E, b.TermAs[Fun[B, B]]("λu:B. u"), e)))
							inverseValue := b.Have(
								"injectivity makes the delta function the inverse image of e",
								"«inverseLift»(e) = δ",
								By(
									identityValue,
									inFree,
									coordinates,
									functions.InverseOnLeft.At(b.TermAs[Set[Fun[B, A]]]("free_module_record(R, E).carrier"), lift, δ)))
							b.Show(
								"the free lift takes that generator to the prescribed value",
								Simp(Fwd(inverseValue), Fwd(functions.ComposeApply)),
								By(Normalized, values, generator, eIn, FreeLiftDelta.Read(target).At(E, φ, e)))
						}))))
		}),
})}

// FreeModuleLift — a linear map u out of the free module on S lifts along
// any linear map p into the same module whose image contains that of u, and
// the generators do the choosing: each u(δ_x) has a preimage θ(x) in W, and
// the extension h of θ to the free module is linear. The composite p ∘ h is
// linear and takes δ_x to p(θ(x)) = u(δ_x), so it agrees with u on the
// generators, and so on the whole free module.
var FreeModuleLift = freeModuleLiftThm{family.Add(registry.ProofEntry{
	Name: "FreeModuleLift",
	Key:  "prop_cca6a3e5a68475ad",
	Reading: "The projectivity of a free module with the basis doing the " +
		"choosing: one preimage per generator, none per element. Over a based " +
		"complex it is the step that builds contractions degree by degree.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀S:set(D). " +
			"∀u:((D → A) → B). " +
			"∀p:(C → B).",
		Hypotheses: []string{
			"module_homomorphism(R, free_module_record(R, S), V, u)",
			"module_homomorphism(R, W, V, p)",
			"∀a:(D → A). a ∈ finite_supp(R.zero, R.carrier, S) ⇒ u(a) ∈ image(p, W.carrier)",
		},
		Conclusion: "∃h:((D → A) → C). " +
			"    module_homomorphism(R, free_module_record(R, S), W, h) ∧ " +
			"    (∀a:(D → A). a ∈ finite_supp(R.zero, R.carrier, S) ⇒ p(h(a)) = u(a))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		S *Expr[Set[D]],
		u *Arrow[Fun[D, A], B],
		p *Arrow[C, B],
		linearU, linearP, onImage Fact,
	) {
		moduleV := module_homomorphism.HomTarget.Read(linearP)
		moduleW := module_homomorphism.HomSource.Read(linearP)
		images := a.Have(
			"the generators lie in the free module, R being commutative, so u carries each into the image of p",
			"∀x:D. x ∈ S ⇒ u(delta_at(x)) ∈ image(p, W.carrier)",
			By(onImage, DeltaAtIn.Read(module.RingOn.Read(moduleV))))
		θ, θDef := a.LetAs[Fun[D, C]]("θ", "λx:D. inverse_on(W.carrier, p, u(delta_at(x)))")
		θIn := a.Have(
			"θ picks a preimage in W of the image of each generator",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ W.carrier",
			By(images, θDef, functions.InverseOnIn))
		h, hDef := a.LetAs[Fun[Fun[D, A], C]]("h", "free_lift(R.zero, W.add, W.zero, W.smul, θ)")
		linear := a.Have(
			"the extension h of θ to the free module is linear",
			"module_homomorphism(R, free_module_record(R, S), W, h)",
			By(Normalized, hDef, θIn, FreeLiftHom.Read(moduleW).At(S, θ)))
		onGenerators := a.Have(
			"h takes the generator δ_x to θ(x), which p takes back to u(δ_x)",
			"∀x:D. x ∈ S ⇒ p(h(delta_at(x))) = u(delta_at(x))",
			By(images, θIn, θDef, hDef, FreeLiftDelta.Read(moduleW), functions.InverseOnRight))
		free := a.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)")
		composite := a.TermAs[Fun[Fun[D, A], B]]("p ∘ h")
		a.Take(h)
		// FreeLiftUnique is cited at S, p ∘ h and u alone: its typed At would
		// also ground f, the member of the free module the goal binds.
		a.Show(
			"h is linear, and p ∘ h, linear as a composite of linear "+
				"maps, agrees with u on the generators, so on the free module",
			By(
				linear,
				linearP,
				linearU,
				onGenerators,
				module_homomorphism.HomCompose.At(R, free, W, V, h, p),
				functions.ComposeApply,
				At(FreeLiftUnique.Read(moduleV), S, composite, u)))
	}),
})}

// ---------------------------------------------------------------------------
// The pushforward along a map of basis sets
// ---------------------------------------------------------------------------

// FreePushforwardDef — `free_pushforward(R, k)`: the pushforward along a
// map k of basis sets, the extension to the free module of the map taking
// x to the generator at k(x).
var FreePushforwardDef = freePushforwardDefThm{family.Define(registry.DefEntry{
	Name:  "FreePushforwardDef",
	Const: "free_pushforward",
	Type:  "ring_ops(A) → (I → E) → (I → A) → E → A",
	Key:   "prop_21c8b66951fe55b2",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:(I → E). " +
			"    free_pushforward(R, k) = " +
			"    free_lift(R.zero, " +
			"        fun_add⟨D:E⟩(R.add), " +
			"        fun_zero⟨D:E⟩(R.zero), " +
			"        fun_smul⟨D:E⟩(R.mul), " +
			"        λx:I. delta_at(R.zero, R.one, k(x)))",
	},
	Deps: []registry.EntryLike{FreeLiftDef, DeltaAtDef},
})}

// FreePushforwardHom — the pushforward along a map k of S into T is a
// homomorphism from the free module on S to the free module on T.
var FreePushforwardHom = freePushforwardHomThm{family.Add(registry.ProofEntry{
	Name: "FreePushforwardHom",
	Key:  "prop_54ee100769cbc012",
	Deps: []registry.EntryLike{
		FreePushforwardDef,
		FreeLiftHom,
		FreeModuleOn,
		DeltaAtIn,
		FreeModuleRecordDef,
		set_basic.InImage,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(I). ∀T:set(E). ∀k:(I → E).",
		Hypotheses: []string{
			"module_on(R, free_module_record(R, S))",
			"image(k, S) ⊆ T",
		},
		Conclusion: "module_homomorphism(R, " +
			"    free_module_record(R, S), " +
			"    free_module_record(R, T), " +
			"    free_pushforward(R, k))",
	},
		"each point x of S goes to the generator at k(x), a member of the free "+
			"module on T since k(x) lies in T (DeltaAtIn); extend by FreeLiftHom"),
})}

// FreePushforwardDelta — the pushforward along k takes the generator at
// a point x of S to the generator at k(x).
var FreePushforwardDelta = freePushforwardDeltaThm{family.Add(registry.ProofEntry{
	Name: "FreePushforwardDelta",
	Key:  "prop_bba22db80bb5d67b",
	Deps: []registry.EntryLike{FreePushforwardDef, FreeLiftDelta, FreeModuleRecordDef},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(I). ∀k:(I → E). ∀x:I.",
		Hypotheses: []string{
			"module_on(R, free_module_record(R, S))",
			"x ∈ S",
		},
		Conclusion: "free_pushforward(R, k, delta_at(x)) = delta_at(k(x))",
	},
		"FreeLiftDelta evaluates the extension at a generator"),
})}

// FreePushforwardCompose — the pushforward along a composite l ∘ k is the
// pushforward along l after the pushforward along k.
var FreePushforwardCompose = freePushforwardComposeThm{family.Add(registry.ProofEntry{
	Name: "FreePushforwardCompose",
	Key:  "prop_b56d541f371b0861",
	Deps: []registry.EntryLike{
		FreePushforwardHom,
		FreePushforwardDelta,
		FreeLiftUnique,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(I). ∀T:set(E). ∀k:(I → E). ∀U:set(D). ∀l:(E → D). ∀u:(I → A).",
		Hypotheses: []string{
			"module_on(R, free_module_record(R, S))",
			"image(k, S) ⊆ T",
			"image(l, T) ⊆ U",
			"u ∈ finite_supp(R.zero, R.carrier, S)",
		},
		Conclusion: "free_pushforward(R, l ∘ k, u) = free_pushforward(R, l, free_pushforward(R, k, u))",
	},
		"as maps of u both sides are homomorphisms out of the free module on S "+
			"(FreePushforwardHom, HomCompose) agreeing on every generator "+
			"(FreePushforwardDelta); FreeLiftUnique extends the equality to the free module"),
})}

// FreePushforwardIdentity — the pushforward along the identity is the
// identity on the free module.
var FreePushforwardIdentity = freePushforwardIdentityThm{family.Add(registry.ProofEntry{
	Name: "FreePushforwardIdentity",
	Key:  "prop_f517be7061403a3e",
	Deps: []registry.EntryLike{
		FreePushforwardHom,
		FreePushforwardDelta,
		FreeLiftUnique,
		module_homomorphism.HomIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(I). ∀u:(I → A).",
		Hypotheses: []string{
			"module_on(R, free_module_record(R, S))",
			"u ∈ finite_supp(R.zero, R.carrier, S)",
		},
		Conclusion: "free_pushforward(R, λx:I. x, u) = u",
	},
		"the pushforward along the identity agrees with the identity homomorphism on "+
			"every generator (FreePushforwardDelta), so on the free module (FreeLiftUnique)"),
})}
