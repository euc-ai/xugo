// double_complex.go — first-quadrant double complexes with shared
// vector operations, their finite diagonal sums, and acyclic assembly;
// the transpose, whose total complex is the original one up to the sign
// (−1)^(pq) on the (p, q) coordinate, so that assembly holds along the
// columns as along the rows; maps of double complexes and their totals;
// and the columnwise cone of a map, whose total complex is the cone of
// the total map. double_total takes the sign on the vertical boundary
// of the column p as a parameter, and a total degree is a module at any
// sign; from the total complex on, every theorem is stated at comm_ring's
// alternating sign (−1)^p, a sign under which the boundary squares to
// zero.

package chain_complex

import (
	"github.com/euc-ai/xugo/ext/on"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"

	. "github.com/euc-ai/xugo/library/authoring"
)

// DoubleComplex — `double_complex(R, V, D, h, v)`: V is an R-module and
// every D(p, q) a submodule of it, every horizontal map h(p + 1, q) and
// vertical map v(p, q + 1) is a homomorphism to the term one step down,
// two horizontal or two vertical maps in a row are zero, and the
// horizontal and vertical maps commute.
var DoubleComplex = doubleComplexThm{family.DefineStructure(registry.DefEntry{
	Name:  "DoubleComplex",
	Const: "double_complex",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"(num → num → set(B)) → " +
		"(num → num → B → B) → " +
		"(num → num → B → B) → " +
		"bool",
	Key:     "prop_5c79e55171fb4be8",
	Subject: "D",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀h v:(num → num → B → B). " +
			"    double_complex(R, V, D, h, v) ⇔ " +
			"    (module_on(R, V)) ∧ " +
			"    (∀p q:num. submodule(R, V, D(p, q))) ∧ " +
			"    (∀p q:num. " +
			"        module_homomorphism(R, " +
			"            restrict_module(V, D(p + 1, q)), " +
			"            restrict_module(V, D(p, q)), " +
			"            h(p + 1, q))) ∧ " +
			"    (∀p q:num. " +
			"        module_homomorphism(R, " +
			"            restrict_module(V, D(p, q + 1)), " +
			"            restrict_module(V, D(p, q)), " +
			"            v(p, q + 1))) ∧ " +
			"    (∀p q:num. ∀x:B. x ∈ D(p + 2, q) ⇒ h(p + 1, q, h(p + 2, q, x)) = V.zero) ∧ " +
			"    (∀p q:num. ∀x:B. x ∈ D(p, q + 2) ⇒ v(p, q + 1, v(p, q + 2, x)) = V.zero) ∧ " +
			"    (∀p q:num. ∀x:B. " +
			"        x ∈ D(p + 1, q + 1) ⇒ h(p + 1, q, v(p + 1, q + 1, x)) = v(p, q + 1, h(p + 1, q + 1, x)))",
	},
})}

// DoubleAmbientModule — the ambient V is a module.
var DoubleAmbientModule = doubleAmbientModuleThm{family.Add(registry.ProofEntry{
	Name:  "DoubleAmbientModule",
	Key:   "prop_8fc9a8ed970b4ab0",
	Build: DoubleComplex.Axiom("module_on(R, V)"),
})}

// DoubleSubmodules — every D(p, q) is a submodule of V.
var DoubleSubmodules = doubleSubmodulesThm{family.Add(registry.ProofEntry{
	Name:  "DoubleSubmodules",
	Key:   "prop_433ca7d25bd566fc",
	Build: DoubleComplex.Axiom("∀p q:num. submodule(R, V, D(p, q))"),
})}

// DoubleHorizontalHom — every horizontal map h(p + 1, q) is a homomorphism from D(p + 1, q) to D(p, q).
var DoubleHorizontalHom = doubleHorizontalHomThm{family.Add(registry.ProofEntry{
	Name: "DoubleHorizontalHom",
	Key:  "prop_ec564e0ce7aca0b1",
	Build: DoubleComplex.Axiom(
		"∀p q:num. " +
			"    module_homomorphism(R, " +
			"        restrict_module(V, D(p + 1, q)), " +
			"        restrict_module(V, D(p, q)), " +
			"        h(p + 1, q))"),
})}

// DoubleVerticalHom — every vertical map v(p, q + 1) is a homomorphism from D(p, q + 1) to D(p, q).
var DoubleVerticalHom = doubleVerticalHomThm{family.Add(registry.ProofEntry{
	Name: "DoubleVerticalHom",
	Key:  "prop_282550e85d4ede1f",
	Build: DoubleComplex.Axiom(
		"∀p q:num. " +
			"    module_homomorphism(R, " +
			"        restrict_module(V, D(p, q + 1)), " +
			"        restrict_module(V, D(p, q)), " +
			"        v(p, q + 1))"),
})}

// DoubleHorizontalTwice — two horizontal maps in a row are zero.
var DoubleHorizontalTwice = doubleHorizontalTwiceThm{family.Add(registry.ProofEntry{
	Name: "DoubleHorizontalTwice",
	Key:  "prop_306f86d4217b7f21",
	Build: DoubleComplex.Axiom(Statement{
		Binders: "∀p q:num. ∀x:B.",
		Hypotheses: []string{
			"x ∈ D(p + 2, q)",
		},
		Conclusion: "h(p + 1, q, h(p + 2, q, x)) = V.zero",
	}),
})}

// DoubleVerticalTwice — two vertical maps in a row are zero.
var DoubleVerticalTwice = doubleVerticalTwiceThm{family.Add(registry.ProofEntry{
	Name: "DoubleVerticalTwice",
	Key:  "prop_f7180e902a8b9b64",
	Build: DoubleComplex.Axiom(Statement{
		Binders: "∀p q:num. ∀x:B.",
		Hypotheses: []string{
			"x ∈ D(p, q + 2)",
		},
		Conclusion: "v(p, q + 1, v(p, q + 2, x)) = V.zero",
	}),
})}

// DoubleCommute — the horizontal and vertical maps commute.
var DoubleCommute = doubleCommuteThm{family.Add(registry.ProofEntry{
	Name: "DoubleCommute",
	Key:  "prop_8f600881d07baff1",
	Build: DoubleComplex.Axiom(Statement{
		Binders: "∀p q:num. ∀x:B.",
		Hypotheses: []string{
			"x ∈ D(p + 1, q + 1)",
		},
		Conclusion: "h(p + 1, q, v(p + 1, q + 1, x)) = v(p, q + 1, h(p + 1, q + 1, x))",
	}),
})}

// DoubleTotalTermsDef — the finite diagonal direct sum, with all coordinates above n zero.
var DoubleTotalTermsDef = doubleTotalTermsDefThm{family.Define(registry.DefEntry{
	Name:  "DoubleTotalTermsDef",
	Const: "double_total_terms",
	Type:  "module_ops(A, B) → (num → num → set(B)) → num → set(num → B)",
	Key:   "prop_aa06ea431da21350",
	Equations: []string{
		"∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀n:num. " +
			"    double_total_terms(V, D, n) = " +
			"    {u:(num → B) | (∀p:num. p ≤ n ⇒ u(p) ∈ D(p, n - p)) ∧ (∀p:num. n < p ⇒ u(p) = V.zero)}",
	},
})}

// DoubleTotalTermsMember — a function on the indices is a total term of
// degree n exactly when its coordinate p ≤ n lies in D(p, n − p) and every
// coordinate past n is zero: membership in the comprehension the
// definition names, read off.
var DoubleTotalTermsMember = doubleTotalTermsMemberThm{family.Add(registry.ProofEntry{
	Name: "DoubleTotalTermsMember",
	Key:  "prop_9423326bb6ad7337",
	Build: family.Theorem("∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀n:num. ∀u:(num → B). "+
		"    u ∈ double_total_terms(V, D, n) ⇔ "+
		"    (∀p:num. p ≤ n ⇒ u(p) ∈ D(p, n - p)) ∧ (∀p:num. n < p ⇒ u(p) = V.zero)",
		func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			D *Expr[Fun2[Nat, Nat, Set[B]]],
			n *Expr[Nat],
			u *Arrow[Nat, B],
		) {
			a.Show(
				"a total term is a point of the comprehension of its two coordinate conditions",
				Unfold(DoubleTotalTermsDef),
				BySets())
		}),
})}

// DoubleBoundaryDef — h plus the signed v on a diagonal; at degree zero it is the zero map.
var DoubleBoundaryDef = doubleBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "DoubleBoundaryDef",
	Const: "double_boundary",
	Type: "module_ops(A, B) → " +
		"(num → num → B → B) → " +
		"(num → num → B → B) → " +
		"(num → A) → " +
		"num → " +
		"(num → B) → " +
		"num → " +
		"B",
	Key: "prop_d1225eefa9cae1af",
	Equations: []string{
		"∀V:module_ops(A, B). ∀h v:(num → num → B → B). ∀s:(num → A). ∀n:num. ∀u:(num → B). ∀p:num. " +
			"    double_boundary(V, h, v, s, n, u, p) = " +
			"    COND(p < n, V.add(h(p + 1, n - (p + 1), u(p + 1)), V.smul(s(p), v(p, n - p, u(p)))), V.zero)",
	},
})}

// DoubleTotalDef — the finite diagonal totalization with common pointwise operations.
var DoubleTotalDef = doubleTotalDefThm{family.Define(registry.DefEntry{
	Name:  "DoubleTotalDef",
	Const: "double_total",
	Type: "module_ops(A, B) → " +
		"(num → num → set(B)) → " +
		"(num → num → B → B) → " +
		"(num → num → B → B) → " +
		"(num → A) → " +
		"complex_ops(A, num → B)",
	Key: "prop_1c47899ca4b3b847",
	Equations: []string{
		"∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀h v:(num → num → B → B). ∀s:(num → A). " +
			"    double_total(V, D, h, v, s) = " +
			"    pack_complex((λu:(num → B). λw:(num → B). λp:num. V.add(u(p), w(p))), " +
			"        (λp:num. V.zero), " +
			"        (λu:(num → B). λp:num. V.neg(u(p))), " +
			"        (λc:A. λu:(num → B). λp:num. V.smul(c, u(p))), " +
			"        double_total_terms(V, D), " +
			"        double_boundary(V, h, v, s))",
	},
	Deps: []registry.EntryLike{ComplexAddDef, DoubleTotalTermsDef, DoubleBoundaryDef},
})}

// DoubleBoundaryCoordinate — the boundary out of degree p + q + 1, read at
// the coordinate p of the diagonal of degree p + q it lands on, is the
// horizontal boundary out of (p + 1, q) plus the signed vertical boundary
// out of (p, q + 1): p is below p + q + 1, so the boundary takes its first
// branch, and the two heights its definition subtracts are q and q + 1.
var DoubleBoundaryCoordinate = doubleBoundaryCoordinateThm{family.Add(registry.ProofEntry{
	Name: "DoubleBoundaryCoordinate",
	Key:  "prop_31f9b5e50a9887ae",
	Build: family.Theorem("∀V:module_ops(A, B). "+
		"∀h v:(num → num → B → B). "+
		"∀s:(num → A). "+
		"∀p q:num. "+
		"∀u:(num → B). "+
		"    double_boundary(V, h, v, s, p + q + 1, u, p) = "+
		"    h(p + 1, q, u(p + 1)) + s(p) • v(p, q + 1, u(p))",
		func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			h, v *Expr[Fun3[Nat, Nat, B, B]],
			s *Arrow[Nat, A],
			p, q *Expr[Nat],
			u *Arrow[Nat, B],
		) {
			onDiagonal := a.Have(
				"p is below p + q + 1, and the source coordinates p + 1 and p sit at heights q and q + 1",
				"p < p + q + 1 ∧ p + q + 1 - (p + 1) = q ∧ p + q + 1 - p = q + 1",
				ByArith())
			a.Show(
				"so the boundary takes its first branch, at those heights",
				Simp(Fwd(DoubleBoundaryDef)),
				By(Normalized, onDiagonal))
		}),
})}

// DoubleBoundaryPast — the boundary out of degree n + 1 vanishes past n,
// the top of the diagonal it lands on: a coordinate p beyond n is not
// below n + 1, so the boundary takes its second branch, zero.
var DoubleBoundaryPast = doubleBoundaryPastThm{family.Add(registry.ProofEntry{
	Name: "DoubleBoundaryPast",
	Key:  "prop_3dc65a801e93dd05",
	Build: family.Theorem(Statement{
		Binders: "∀V:module_ops(A, B). ∀h v:(num → num → B → B). ∀s:(num → A). ∀n p:num. ∀u:(num → B).",
		Hypotheses: []string{
			"n < p",
		},
		Conclusion: "double_boundary(V, h, v, s, n + 1, u, p) = V.zero",
	},
		func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			h, v *Expr[Fun3[Nat, Nat, B, B]],
			s *Arrow[Nat, A],
			n, p *Expr[Nat],
			u *Arrow[Nat, B],
			past Fact,
		) {
			a.Have(
				"a coordinate p past n is not below n + 1",
				"¬(p < n + 1)",
				ByArith(past))
			a.Show(
				"so the boundary takes its second branch, zero",
				Simp(Fwd(DoubleBoundaryDef)),
				Refl())
		}),
})}

// DoubleTotalCoordinate — a total term of degree p + q has its coordinate
// p in D(p, q): the coordinate p lies on that diagonal, and the height its
// definition subtracts, p + q − p, is q.
var DoubleTotalCoordinate = doubleTotalCoordinateThm{family.Add(registry.ProofEntry{
	Name: "DoubleTotalCoordinate",
	Key:  "prop_cc07d046aa4f6cdb",
	Build: family.Theorem(Statement{
		Binders: "∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀p q:num. ∀u:(num → B).",
		Hypotheses: []string{
			"u ∈ double_total_terms(V, D, p + q)",
		},
		Conclusion: "u(p) ∈ D(p, q)",
	},
		func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			D *Expr[Fun2[Nat, Nat, Set[B]]],
			p, q *Expr[Nat],
			u *Arrow[Nat, B],
			total Fact,
		) {
			onDiagonal := a.Have(
				"p lies on the diagonal of degree p + q, at height q",
				"p ≤ p + q ∧ p + q - p = q",
				ByArith())
			a.Show(
				"so the total term places its coordinate p in D(p, q)",
				total.Simp(Fwd(DoubleTotalTermsDef)),
				BySets(total, onDiagonal))
		}),
})}

// DoubleTotalPast — a total term of degree n vanishes at every coordinate
// past n: that is the second of the two conditions its definition places
// on it.
var DoubleTotalPast = doubleTotalPastThm{family.Add(registry.ProofEntry{
	Name: "DoubleTotalPast",
	Key:  "prop_2b8811771cc1d44",
	Build: family.Theorem(Statement{
		Binders: "∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀n p:num. ∀u:(num → B).",
		Hypotheses: []string{
			"u ∈ double_total_terms(V, D, n)",
			"n < p",
		},
		Conclusion: "u(p) = V.zero",
	},
		func(
			a *Argument,
			V *Expr[ModuleOps[A, B]],
			D *Expr[Fun2[Nat, Nat, Set[B]]],
			n, p *Expr[Nat],
			u *Arrow[Nat, B],
			given Fact,
		) {
			a.Show(
				"the total term's definition makes it vanish past n",
				given.Simp(Fwd(DoubleTotalTermsDef)),
				BySets(given))
		}),
})}

// DoubleTotalModule — a total degree of the diagonal totalization is a
// module once V is one and every D(p, q) a submodule of it: its terms are
// a submodule of the functions on 0 .. n into V, a total term taking its
// coordinates in the submodules D(p, n − p) and zero past n, so the
// coordinatewise operations keep it a total term.
var DoubleTotalModule = doubleTotalModuleThm{family.Add(registry.ProofEntry{
	Name: "DoubleTotalModule",
	Key:  "prop_7964388786a5731d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀D:(num → num → set(B)). " +
			"∀h v:(num → num → B → B). " +
			"∀s:(num → A). " +
			"∀n:num.",
		Hypotheses: []string{
			"module_on(R, V)",
			"∀p q:num. submodule(R, V, D(p, q))",
		},
		Conclusion: "module_on(R, complex_module(double_total(V, D, h, v, s), n))",
		Abbrev: Abbrev{
			{Name: "totalAmbient", Text: "function_module(V, 0 .. n)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			D *Expr[Fun2[Nat, Nat, Set[B]]],
			h, v *Expr[Fun3[Nat, Nat, B, B]],
			s *Arrow[Nat, A],
			n *Expr[Nat],
			moduleV module.ModuleFact[on.R, on.V],
			submodules Fact,
		) {
			ambientModule := a.Have(
				"the finite supported function module is a module",
				"module_on(R, «totalAmbient»)",
				By(moduleV, function_module.FunModuleOn.At(R, V, a.TermAs[Set[Nat]]("0 .. n"))))
			recordIdentity := a.Have(
				"the total degree module restricts the supported function module",
				"complex_module(double_total(V, D, h, v, s), n) = "+
					"restrict_module(«totalAmbient», double_total_terms(V, D, n))",
				Simp(
					Fwd(DoubleTotalDef),
					Fwd(ComplexModuleDef),
					Fwd(function_module.FunctionModuleDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(module_record.ModAddDef),
					Fwd(module_record.ModZeroDef),
					Fwd(module_record.ModNegDef),
					Fwd(module_record.ModSmulDef)),
				Unfold(function_module.FunAddDef),
				Unfold(function_module.FunZeroDef),
				Unfold(function_module.FunNegDef),
				Unfold(function_module.FunSmulDef))
			ambientMembers := a.Have(
				"ambient functions take values in V and vanish outside the degree interval",
				"∀u:(num → B). "+
					"    u ∈ «totalAmbient».carrier ⇔ "+
					"    (∀p:num. u(p) ∈ V.carrier) ∧ (∀p:num. p ∉ 0 .. n ⇒ u(p) = V.zero)",
				Simp(
					Fwd(function_module.FunctionModuleDef),
					Fwd(module_record.ModCarrierDef),
					Fwd(function_module.FunModuleDef)),
				BySets())
			totalSubset := a.Have(
				"every total-degree vector belongs to the supported function module",
				"double_total_terms(V, D, n) ⊆ «totalAmbient».carrier",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, B]]("u")
					inTotal := b.Simplified(b.Assume(), Fwd(DoubleTotalTermsMember))
					parts := b.Conjuncts(
						inTotal,
						"the coordinates lie in their bidegrees",
						"the coordinates vanish past n")
					ambientReading := b.Simplified(
						ambientMembers,
						Fwd(function_module.FunctionModuleDef),
						Fwd(module_record.ModCarrierDef))
					b.Show(
						"the bidegree carriers and zero tail give the ambient carrier conditions",
						Simp(Fwd(ambientReading)),
						SplitConj(
							Case(
								"every coordinate lies in V",
								Derive(func(c *Argument) {
									p := c.FixAs[Nat]("p")
									c.Cases(c.TermAs[Bool]("p ≤ n"))
									c.When(
										"coordinates in range lie in submodules of V",
										func(d *Argument, bound Fact) {
											d.Show(
												"the bidegree submodule lies in V",
												BySets(
													bound,
													parts[0].At(p),
													submodules.At(p, d.TermAs[Nat]("n - p")),
													submodule.SubmoduleSubset.At(R, V, d.TermAs[Set[B]]("D(p, n - p)"))))
										})
									c.Otherwise(
										"coordinates past n are the zero of V",
										func(d *Argument, beyond Fact) {
											beyond = d.Simplified(beyond, Fwd(nat_order.NotLessEq))
											d.Show(
												"zero lies in the ambient module",
												By(Normalized, group.OneIn.Read(module.AddGroupOn.Read(moduleV)), beyond, parts[1].At(p)))
										})
								})),
							Case(
								"the vector vanishes outside the degree interval",
								Simp(Fwd(num_segment.MembershipFromZero), Fwd(nat_order.NotLessEq)),
								By(parts[1]))))
				}))
			zeroClosed := a.Have(
				"the supported zero vector has every required bidegree",
				"«totalAmbient».zero ∈ double_total_terms(V, D, n)",
				Simp(
					Fwd(DoubleTotalTermsMember),
					Fwd(function_module.FunctionModuleDef),
					Fwd(module_record.ModZeroDef),
					Fwd(function_module.FunZeroDef)),
				By(submodules, At(submodule.SubmoduleZero, R, V)))
			addClosed := a.Have(
				"total-degree vectors are closed under addition",
				Statement{
					Binders:    "∀u w:(num → B).",
					Hypotheses: []string{"u ∈ double_total_terms(V, D, n)", "w ∈ double_total_terms(V, D, n)"},
					Conclusion: "«totalAmbient».add(u, w) ∈ double_total_terms(V, D, n)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, B]]("u")
					b.FixAs[Fun[Nat, B]]("w")
					inTotal := b.Simplified(b.Assume(), Fwd(DoubleTotalTermsMember))
					parts := b.Conjuncts(
						inTotal,
						"u lies in each bidegree",
						"u vanishes past n",
						"w lies in each bidegree",
						"w vanishes past n")
					b.Show(
						"addition preserves the bidegree carriers and the zero tail",
						Simp(
							Fwd(DoubleTotalTermsMember),
							Fwd(function_module.FunctionModuleDef),
							Fwd(module_record.ModAddDef),
							Fwd(function_module.FunAddDef)),
						SplitConj(
							Case(
								"addition preserves each bidegree submodule",
								Derive(func(c *Argument) {
									p := c.FixAs[Nat]("p")
									bound := c.Assume()
									c.Show(
										"the sum lies in the same bidegree",
										By(
											bound,
											parts[0].At(p),
											parts[2].At(p),
											submodules.At(p, c.TermAs[Nat]("n - p")),
											submodule.SubmoduleAdd.At(
												R, V, c.TermAs[Set[B]]("D(p, n - p)"), c.TermAs[B]("u(p)"), c.TermAs[B]("w(p)"))))
								})),
							Case(
								"the sum remains zero past n",
								Derive(func(c *Argument) {
									p := c.FixAs[Nat]("p")
									beyond := c.Assume()
									c.Show(
										"the two zero coordinates add to zero",
										By(
											group.OneIn.Read(module.AddGroupOn.Read(moduleV)),
											group.LeftIdentityOn.Read(module.AddGroupOn.Read(moduleV)),
											beyond,
											parts[1].At(p),
											parts[3].At(p)))
								}))))
				}))
			scalarClosed := a.Have(
				"total-degree vectors are closed under scalar multiplication",
				Statement{
					Binders:    "∀c:A. ∀u:(num → B).",
					Hypotheses: []string{"c ∈ R.carrier", "u ∈ double_total_terms(V, D, n)"},
					Conclusion: "«totalAmbient».smul(c, u) ∈ double_total_terms(V, D, n)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					b.FixAs[Fun[Nat, B]]("u")
					inTotal := b.Simplified(b.Assume(), Fwd(DoubleTotalTermsMember))
					parts := b.Conjuncts(
						inTotal,
						"the scalar lies in R",
						"u lies in each bidegree",
						"u vanishes past n")
					b.Show(
						"scaling preserves the bidegree carriers and the zero tail",
						Simp(
							Fwd(DoubleTotalTermsMember),
							Fwd(function_module.FunctionModuleDef),
							Fwd(module_record.ModSmulDef),
							Fwd(function_module.FunSmulDef)),
						SplitConj(
							Case(
								"scaling preserves each bidegree submodule",
								Derive(func(d *Argument) {
									p := d.FixAs[Nat]("p")
									bound := d.Assume()
									d.Show(
										"the scaled coordinate lies in the same bidegree",
										By(
											parts[0],
											bound,
											parts[1].At(p),
											submodules.At(p, d.TermAs[Nat]("n - p")),
											submodule.SubmoduleSmul.At(R, V, d.TermAs[Set[B]]("D(p, n - p)"), c, d.TermAs[B]("u(p)"))))
								})),
							Case(
								"the scaled vector remains zero past n",
								Derive(func(d *Argument) {
									p := d.FixAs[Nat]("p")
									beyond := d.Assume()
									d.Show(
										"a scalar multiple of zero is zero",
										By(Normalized, parts[0], beyond, parts[2].At(p), module.SmulZero.Read(moduleV).AsFact().At(c)))
								}))))
				}))
			totalSubmodule := a.Have(
				"the total-degree vectors form a submodule of the supported function module",
				"submodule(R, «totalAmbient», double_total_terms(V, D, n))",
				By(
					ambientModule,
					totalSubset,
					zeroClosed,
					addClosed,
					scalarClosed,
					submodule.SubmoduleCriterion.At(
						R,
						a.TermAs[ModuleOps[A, Fun[Nat, B]]]("«totalAmbient»"),
						a.TermAs[Set[Fun[Nat, B]]]("double_total_terms(V, D, n)"))))
			a.Show(
				"restriction to the total-degree submodule gives the required module",
				Simp(Fwd(recordIdentity)),
				By(
					ambientModule,
					totalSubmodule,
					submodule.SubmoduleModuleOn.At(
						R,
						a.TermAs[ModuleOps[A, Fun[Nat, B]]]("«totalAmbient»"),
						a.TermAs[Set[Fun[Nat, B]]]("double_total_terms(V, D, n)"))))
		}),
})}

// DoubleTotalComplex — the total complex of a double complex is a chain
// complex, its vertical boundaries signed by the alternating sign. Every
// total degree is a module (DoubleTotalModule). At a coordinate p ≤ n of
// the degree n + 1, written n = p + q, the boundary is h(p + 1, q) on
// u(p + 1) ∈ D(p + 1, q) plus (−1)^p times v(p, q + 1) on
// u(p) ∈ D(p, q + 1), so it is linear and lands in D(p, q); past the
// diagonal it is zero. Applied twice at (p, q), h after h and v after v
// vanish, and the two mixed terms (−1)^(p+1) • h(v(y)) and
// (−1)^p • v(h(y)) cancel, h and v commuting and adjacent signs being
// negatives.
var DoubleTotalComplex = doubleTotalComplexThm{family.Add(registry.ProofEntry{
	Name: "DoubleTotalComplex",
	Key:  "prop_8970627b454e0d62",
	Build: DoubleComplex.Law("chain_complex(R, «doubleTotal»)",
		func(a *Argument, double DoubleComplexFact[on.R, on.V]) {
			moduleV := DoubleAmbientModule.Read(double)
			submodules := DoubleSubmodules.Read(double)
			horizontal, vertical := DoubleHorizontalHom.Read(double), DoubleVerticalHom.Read(double)
			horizontalTwice, verticalTwice, commute :=
				DoubleHorizontalTwice.Read(double), DoubleVerticalTwice.Read(double), DoubleCommute.Read(double)
			ring := module.RingOn.Read(moduleV)
			additive := module.AddGroupOn.Read(moduleV)
			V, D := a.TermAs[ModuleOps[A, B]]("V"), a.TermAs[Fun2[Nat, Nat, Set[B]]]("D")
			h, v := a.TermAs[Fun3[Nat, Nat, B, B]]("h"), a.TermAs[Fun3[Nat, Nat, B, B]]("v")
			s := a.TermAs[Fun[Nat, A]]("alternating_sign")

			signFacts := a.Have(
				"every sign is a scalar, and cancels against the next",
				"∀k:num. alternating_sign(k) ∈ R.carrier ∧ alternating_sign(k + 1) + alternating_sign(k) = R.zero",
				By(comm_ring.AlternatingSignIn.Read(ring), comm_ring.AlternatingSignSuc.Read(ring)))

			zeroSum := a.Have(
				"zero plus zero is zero",
				"V.zero + V.zero = V.zero",
				By(group.LeftIdentityOn.Read(additive), group.OneIn.Read(additive)))
			terms := a.Have(
				"every total degree is a module",
				"∀n:num. module_on(R, complex_module(«doubleTotal», n))",
				By(DoubleTotalModule, moduleV, submodules))

			// A total term read at a coordinate (p, q) of its diagonal: the
			// boundary there and the term holding the coordinate, and past n
			// the boundary out of degree n + 1 vanishing. The term's
			// coordinate spells its degree at its own (p, q), (p + 1) + q for
			// the coordinate p + 1 of a term of degree p + q + 1; the chase
			// decides that guard at the canonical degree, where both
			// spellings are one.
			boundaryAt := func(p, q *Expr[Nat], u Typed[Fun[Nat, B]]) Fact {
				return DoubleBoundaryCoordinate.At(V, h, v, s, p, q, u)
			}
			termAt := func(p, q *Expr[Nat], u Typed[Fun[Nat, B]]) Fact {
				return DoubleTotalCoordinate.At(V, D, p, q, u)
			}
			boundaryPast := func(n, p *Expr[Nat], u Typed[Fun[Nat, B]]) Fact {
				return DoubleBoundaryPast.At(V, h, v, s, n, p, u)
			}

			linear := a.Have(
				"every total boundary is linear from degree n + 1 to degree n",
				"∀n:num. "+
					"    module_homomorphism(R, "+
					"        complex_module(«doubleTotal», n + 1), "+
					"        complex_module(«doubleTotal», n), "+
					"        double_boundary(V, h, v, alternating_sign, n + 1))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Do(Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)), SplitConjAll(
						Case(
							"the degree n + 1 is a module",
							By(terms)),
						Case(
							"so is the degree n",
							By(terms)),
						Case(
							"the boundary carries the degree n + 1 into the degree n",
							Unfold(ComplexModuleDef),
							Derive(func(c *Argument) {
								u := c.FixAs[Fun[Nat, B]]("u")
								total := c.Assume()
								c.Do(Simp(Fwd(DoubleTotalTermsMember)), SplitConj(
									Case(
										"on the diagonal, at n = p + q, h(p + 1, q) and the signed v(p, q + 1) land in D(p, q)",
										Derive(func(d *Argument) {
											p := d.FixAs[Nat]("p")
											q, atHeight := d.UnpackAs[Nat](d.Simplified(d.Assume(), Fwd(nat_order.LessEqExists)), "q")
											p1, q1 := d.TermAs[Nat]("p + 1"), d.TermAs[Nat]("q + 1")
											nextIn, hereIn := termAt(p1, q, u), termAt(p, q1, u)
											d.Show(
												"u(p + 1) and u(p) lie in D(p + 1, q) and D(p, q + 1), the height p + q − p being q",
												atHeight.Rw(),
												Simp(Fwd(nat_monus.AddSubLeftCancel)),
												ByChase(
													Depth(0),
													boundaryAt(p, q, u),
													nextIn,
													hereIn,
													horizontal.At(p, q),
													vertical.At(p, q),
													signFacts.At(p),
													total))
										})),
									Case(
										"past n each coordinate of the boundary is zero",
										By(DoubleBoundaryPast)),
								))
							})),
						Case(
							"the boundary is additive",
							Unfold(ComplexModuleDef),
							Derive(func(c *Argument) {
								u := c.FixAs[Fun[Nat, B]]("u")
								w := c.FixAs[Fun[Nat, B]]("w")
								totals := c.Assume()
								c.Do(Funext())
								p := c.FixAs[Nat]("p")
								sum := c.TermAs[Fun[Nat, B]]("λi:num. u(i) + w(i)")
								c.Cases(c.Term("p ≤ n"))
								c.When(
									"on the diagonal, at n = p + q, h, v and the scaling by alternating_sign(p) are additive",
									func(d *Argument, below Fact) {
										q, atHeight := d.UnpackAs[Nat](d.Simplified(below, Fwd(nat_order.LessEqExists)), "q")
										p1, q1 := d.TermAs[Nat]("p + 1"), d.TermAs[Nat]("q + 1")
										uNextIn, uHereIn := termAt(p1, q, u), termAt(p, q1, u)
										wNextIn, wHereIn := termAt(p1, q, w), termAt(p, q1, w)
										d.Show(
											"so the boundary of u + w is the sum of the boundaries",
											atHeight.Rw(),
											ByChase(
												Depth(0),
												boundaryAt(p, q, sum),
												boundaryAt(p, q, u),
												boundaryAt(p, q, w),
												uNextIn,
												uHereIn,
												wNextIn,
												wHereIn,
												horizontal.At(p, q),
												vertical.At(p, q),
												signFacts.At(p),
												totals))
									})
								c.Otherwise(
									"past n the three boundaries are zero, and zero is zero plus zero",
									func(d *Argument, offDiagonal Fact) {
										past := d.Have(
											"p lies past n",
											"n < p",
											ByArith(offDiagonal))
										d.Show(
											"so the boundary of u + w is the sum of the boundaries",
											By(boundaryPast(n, p, sum), boundaryPast(n, p, u), boundaryPast(n, p, w), past, zeroSum))
									})
							})),
						Case(
							"the boundary commutes with scaling",
							Unfold(ComplexModuleDef),
							Derive(func(c *Argument) {
								scalar := c.FixAs[A]("c")
								u := c.FixAs[Fun[Nat, B]]("u")
								given := c.Assume()
								c.Do(Funext())
								p := c.FixAs[Nat]("p")
								scaled := c.TermAs[Fun[Nat, B]]("λi:num. c • u(i)")
								c.Cases(c.Term("p ≤ n"))
								c.When(
									"on the diagonal, at n = p + q, h and v commute with "+
										"c, and so does the scaling by alternating_sign(p)",
									func(d *Argument, below Fact) {
										q, atHeight := d.UnpackAs[Nat](d.Simplified(below, Fwd(nat_order.LessEqExists)), "q")
										p1, q1 := d.TermAs[Nat]("p + 1"), d.TermAs[Nat]("q + 1")
										nextIn, hereIn := termAt(p1, q, u), termAt(p, q1, u)
										d.Show(
											"so the boundary of c • u is c times the boundary of u",
											atHeight.Rw(),
											ByChase(
												Depth(0),
												boundaryAt(p, q, scaled),
												boundaryAt(p, q, u),
												nextIn,
												hereIn,
												horizontal.At(p, q),
												vertical.At(p, q),
												signFacts.At(p),
												given))
									})
								c.Otherwise(
									"past n both boundaries are zero, and c • V.zero is zero",
									func(d *Argument, offDiagonal Fact) {
										past := d.Have(
											"p lies past n",
											"n < p",
											ByArith(offDiagonal))
										cIn := d.MemberOf[on.R](scalar, d.Conjuncts(
											given,
											"c is a scalar",
											"u is a total term")[0])
										d.Show(
											"so the boundary of c • u is c times the boundary of u",
											By(boundaryPast(n, p, scaled), boundaryPast(n, p, u), past, module.SmulZero.Read(moduleV).At(cIn)))
									})
							})),
					))
				}))

			// The boundary squares to zero, first at a coordinate (p, q) of
			// the double complex, then on a total term.
			local := a.Have(
				"at a coordinate p of the diagonal of degree p + q + 2 the boundary applied twice vanishes",
				Statement{
					Binders: "∀p q:num. ∀x y z:B.",
					Hypotheses: []string{
						"x ∈ D(p + 2, q)",
						"y ∈ D(p + 1, q + 1)",
						"z ∈ D(p, q + 2)",
					},
					Conclusion: "h(p + 1, q, h(p + 2, q, x) + alternating_sign(p + 1) • v(p + 1, q + 1, y)) + " +
						"alternating_sign(p) • v(p, q + 1, h(p + 1, q + 1, y) + alternating_sign(p) • v(p, q + 2, z)) = " +
						"V.zero",
				},
				Derive(func(b *Argument) {
					p, q := b.FixAs[Nat]("p"), b.FixAs[Nat]("q")
					x, y, z := b.FixAs[B]("x"), b.FixAs[B]("y"), b.FixAs[B]("z")
					in := b.Conjuncts(
						b.Assume(),
						"x lies in D(p + 2, q)",
						"y lies in D(p + 1, q + 1)",
						"z lies in D(p, q + 2)")
					p1, q1 := b.TermAs[Nat]("p + 1"), b.TermAs[Nat]("q + 1")
					first := b.Have(
						"h after h kills x, so the first summand is alternating_sign(p + 1) • h(v(y))",
						"h(p + 1, q, h(p + 2, q, x) + alternating_sign(p + 1) • v(p + 1, q + 1, y)) = "+
							"alternating_sign(p + 1) • h(p + 1, q, v(p + 1, q + 1, y))",
						ByChase(
							Depth(0),
							horizontal.At(p, q),
							horizontal.At(p1, q),
							vertical.At(p1, q),
							horizontalTwice.At(p, q, x),
							signFacts.At(p1),
							in[0],
							in[1]))
					second := b.Have(
						"v after v kills z, and v after h is h after v, so "+
							"the second summand is alternating_sign(p) • h(v(y))",
						"alternating_sign(p) • v(p, q + 1, h(p + 1, q + 1, y) + alternating_sign(p) • v(p, q + 2, z)) = "+
							"alternating_sign(p) • h(p + 1, q, v(p + 1, q + 1, y))",
						ByChase(
							Depth(0),
							vertical.At(p, q),
							vertical.At(p, q1),
							horizontal.At(p, q1),
							commute.At(p, q, y),
							verticalTwice.At(p, q, z),
							signFacts.At(p),
							in[1],
							in[2]))
					b.Show(
						"the two mixed terms cancel, adjacent signs being negatives",
						first.Rw(),
						second.Rw(),
						ByChase(
							Depth(0),
							horizontal.At(p, q),
							vertical.At(p1, q),
							signFacts.At(p),
							signFacts.At(p1),
							in[1]))
				}))
			square := a.Have(
				"two total boundaries in a row vanish",
				Statement{
					Binders: "∀n:num. ∀u:(num → B).",
					Hypotheses: []string{
						"u ∈ double_total_terms(V, D, n + 2)",
					},
					Conclusion: "double_boundary(V, " +
						"    h, " +
						"    v, " +
						"    alternating_sign, " +
						"    n + 1, " +
						"    double_boundary(V, h, v, alternating_sign, n + 2, u)) = " +
						"λp:num. V.zero",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					u := b.FixAs[Fun[Nat, B]]("u")
					total := b.Assume()
					b.Do(Funext())
					p := b.FixAs[Nat]("p")
					b.Cases(b.Term("p ≤ n"))
					b.When(
						"on the diagonal, at n = p + q, it is the local square at (p, q)",
						func(c *Argument, below Fact) {
							q, atHeight := c.UnpackAs[Nat](c.Simplified(below, Fwd(nat_order.LessEqExists)), "q")
							p1, p2, q1, q2 :=
								c.TermAs[Nat]("p + 1"), c.TermAs[Nat]("p + 2"), c.TermAs[Nat]("q + 1"), c.TermAs[Nat]("q + 2")
							c.Do(atHeight.Rw())
							xIn, yIn, zIn := termAt(p2, q, u), termAt(p1, q1, u), termAt(p, q2, u)
							inner := c.TermAs[Fun[Nat, B]]("double_boundary(V, h, v, alternating_sign, p + q + 2, u)")
							c.Show(
								"the boundary twice at (p, q), read at (p + 1, q) and (p, q + "+
									"1) inside, is the local square at u(p + 2), u(p + 1) and u(p)",
								ByChase(
									Depth(0),
									local.At(p, q, c.TermAs[B]("u(p + 2)"), c.TermAs[B]("u(p + 1)"), c.TermAs[B]("u(p)")),
									xIn,
									yIn,
									zIn,
									total,
									boundaryAt(p, q, inner),
									boundaryAt(p1, q, u),
									boundaryAt(p, q1, u),
									horizontal.At(p, q),
									horizontal.At(p1, q),
									horizontal.At(p, q1),
									vertical.At(p, q),
									vertical.At(p1, q),
									vertical.At(p, q1),
									signFacts.At(p),
									signFacts.At(p1)))
						})
					b.Otherwise(
						"past n the outer boundary is zero",
						func(c *Argument, offDiagonal Fact) {
							past := c.Have(
								"p lies past n",
								"n < p",
								ByArith(offDiagonal))
							inner := c.TermAs[Fun[Nat, B]]("double_boundary(V, h, v, alternating_sign, n + 2, u)")
							c.Show(
								"so the boundary twice is zero there",
								By(boundaryPast(n, p, inner), past))
						})
				}))

			a.Show(
				"so the total complex satisfies the three laws of a chain complex",
				By(terms, linear, square, ChainComplex))
		}),
})}

// AcyclicAssembly — a double complex whose rows are exact, h(1, q) mapping
// D(1, q) onto D(0, q) included, has an exact total complex: in every
// degree its cycles are its boundaries.
var AcyclicAssembly = acyclicAssemblyThm{family.Add(registry.ProofEntry{
	Name: "AcyclicAssembly",
	Key:  "prop_66a5687216b7986c",
	Deps: []registry.EntryLike{
		DoubleTotalComplex,
		DoubleTotalDef,
		DoubleTotalTermsMember,
		DoubleTotalCoordinate,
		DoubleTotalPast,
		DoubleBoundaryCoordinate,
		DoubleBoundaryPast,
		CyclesDef,
		BoundariesDef,
		module_homomorphism.ExactAtDef,
		set_basic.InImage,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"∀p q:num. exact_at(V.zero, D(p + 2, q), D(p + 1, q), h(p + 2, q), h(p + 1, q))",
			"∀q:num. image(h(1, q), D(1, q)) = D(0, q)",
		},
		Conclusion: "cycles(«doubleTotal», n) = boundaries(«doubleTotal», n)",
	}),
		"Eliminate a total cycle one diagonal component at a time using exactness of "+
			"the horizontal rows, including surjectivity onto degree zero. The correction "+
			"moves the remaining component to the next horizontal degree. A diagonal has "+
			"only n+1 positions, so the process terminates and constructs a preimage."),
})}

// DoubleEdgeDef — the augmentation reads the q=0 edge of the diagonal.
var DoubleEdgeDef = doubleEdgeDefThm{family.Define(registry.DefEntry{
	Name: "DoubleEdgeDef", Const: "double_edge", Type: "(num → B → C) → num → (num → B) → C",
	Key:       "prop_3a0242acffba5caa",
	Equations: []string{"∀a:(num → B → C). ∀n:num. ∀u:(num → B). double_edge(a, n, u) = a(n, u(n))"},
	Deps:      []registry.EntryLike{},
})}

// ColumnCycleVanishing — a cycle of degree n of the total complex
// vanishing at every coordinate from m ≤ n on is a boundary, when the
// columns are exact above the bottom row.
var ColumnCycleVanishing = columnCycleVanishingThm{family.Add(registry.ProofEntry{
	Name: "ColumnCycleVanishing",
	Key:  "prop_f539977b74741a28",
	Deps: []registry.EntryLike{
		DoubleTotalComplex,
		DoubleTotalDef,
		DoubleTotalTermsMember,
		DoubleTotalCoordinate,
		DoubleTotalPast,
		DoubleBoundaryCoordinate,
		DoubleBoundaryPast,
		CyclesDef,
		BoundariesDef,
		CycleCorrection,
		BoundariesSubsetCycles,
		CyclesSubmodule,
		module_homomorphism.ExactAtDef,
		module.SmulMul,
		module.SmulOne,
		comm_ring.AlternatingSignSquare,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀n m:num. ∀u:(num → B).",
		Hypotheses: []string{
			"∀p q:num. exact_at(V.zero, D(p, q + 2), D(p, q + 1), v(p, q + 2), v(p, q + 1))",
			"m ≤ n",
			"u ∈ cycles(«doubleTotal», n)",
			"∀p:num. m ≤ p ⇒ u(p) = V.zero",
		},
		Conclusion: "u ∈ boundaries(«doubleTotal», n)",
	}),
		"Induction on m. At m = 0 the cycle is the zero diagonal, the boundary of zero. From m "+
			"to m + 1 ≤ n: the coordinate above m vanishes, so the cycle condition at coordinate m "+
			"reads alternating_sign(m) • v(m, n − m)(u(m)) = V.zero, and since alternating_sign(m) "+
			"alternating_sign(m) = R.one (AlternatingSignSquare), u(m) lies in the kernel of v(m, "+
			"n − m); column exactness at D(m, n − m) gives u(m) = v(m, n − m + 1)(y). Subtracting "+
			"the boundary of the diagonal of degree n + 1 holding alternating_sign(m) • y at m and "+
			"zero elsewhere leaves a cycle vanishing at every p ≥ m (CycleCorrection: it is a "+
			"cycle, and a boundary only if u is), a boundary by the hypothesis of induction."),
})}

// AugmentedCycleLift — when the columns of a double complex are exact and
// augmented at their foot by maps a(p) onto the terms of a complex E,
// commuting with the boundaries, every cycle of E is the edge a(n)(u(n))
// of a cycle u of the total complex.
var AugmentedCycleLift = augmentedCycleLiftThm{family.Add(registry.ProofEntry{
	Name: "AugmentedCycleLift",
	Key:  "prop_6c1a574ae16b5402",
	Deps: []registry.EntryLike{
		DoubleTotalComplex,
		DoubleTotalDef,
		DoubleTotalTermsMember,
		DoubleTotalCoordinate,
		DoubleTotalPast,
		DoubleBoundaryCoordinate,
		DoubleBoundaryPast,
		CyclesDef,
		module_homomorphism.ExactAtDef,
		set_basic.InImage,
		module.SmulMul,
		module.SmulOne,
		comm_ring.AlternatingSignSquare,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀E:complex_ops(A, C). ∀a:(num → B → C). ∀n:num. ∀e:C.",
		Hypotheses: []string{
			"chain_complex(R, E)",
			"∀p:num. module_homomorphism(R, restrict_module(V, D(p, 0)), complex_module(E, p), a(p))",
			"∀p:num. image(a(p), D(p, 0)) = E.terms(p)",
			"∀p:num. exact_at(E.zero, D(p, 1), D(p, 0), v(p, 1), a(p))",
			"∀p q:num. exact_at(V.zero, D(p, q + 2), D(p, q + 1), v(p, q + 2), v(p, q + 1))",
			"∀p:num. ∀x:B. x ∈ D(p + 1, 0) ⇒ E.d(p + 1, a(p + 1, x)) = a(p, h(p + 1, 0, x))",
			"e ∈ cycles(E, n)",
		},
		Conclusion: "∃u:(num → B). u ∈ cycles(«doubleTotal», n) ∧ a(n, u(n)) = e",
	}),
		"At degree 0 put a preimage of e under a(0) at the coordinate 0. Above, put at the "+
			"coordinate n an x with a(n)(x) = e, a(n) being onto E.terms(n). Going down the diagonal, "+
			"the coordinate k < n is −alternating_sign(k) • y with v(k, n − k)(y) the obstruction h(k + "+
			"1, n − k − 1)(u(k + 1)): at k = n − 1 the square makes a(n − 1) kill it, E.d(n) killing e, "+
			"and exactness at D(n − 1, 0) supplies y; below, v(k, n − k − 1) kills it: through the "+
			"commuting square it is h applied to v(k + 1, n − k − 1)(u(k + 1)), which the step at k + 1 "+
			"fixed to −alternating_sign(k + 1) • h(k + 2, n − k − 2)(u(k + 2)), and h ∘ h = 0; column "+
			"exactness then supplies y. An existential induction on the number of coordinates fixed "+
			"from the top — a partial diagonal whose boundary vanishes above k extends one coordinate "+
			"down — gives u with no recursion over choices; every coordinate of its boundary vanishes, "+
			"alternating_sign(k) alternating_sign(k) being R.one (AlternatingSignSquare)."),
})}

// AugmentedAssembly — the edge u ↦ a(n)(u(n)) is a chain map, linear on
// each diagonal and commuting with the boundaries because a(n) kills the
// vertical part (−1)^n • v(n, 1)(u(n)) of the boundary's top coordinate and
// carries the horizontal part to the boundary of E. It is an isomorphism
// on homology: every cycle of E lifts to a total cycle (AugmentedCycleLift),
// and a total cycle u whose edge is a boundary E.d(n + 1)(a(n + 1)(x)) is
// corrected by the boundary of the diagonal z holding x at n + 1 and
// (−1)^n • y at n, v(n, 1)(y) = u(n) − h(n + 1, 0)(x) by the augmented
// exactness; the corrected cycle vanishes from the coordinate n on, so it
// is a boundary (ColumnCycleVanishing), and so is u.
var AugmentedAssembly = augmentedAssemblyThm{family.Add(registry.ProofEntry{
	Name: "AugmentedAssembly",
	Key:  "prop_79f3d69bd91d4517",
	Build: DoubleComplex.Law(Statement{
		Binders: "∀E:complex_ops(A, C). ∀a:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, E)",
			"(∀p:num. module_homomorphism(R, restrict_module(V, D(p, 0)), complex_module(E, p), a(p))) ∧ " +
				"(∀p:num. image(a(p), D(p, 0)) = E.terms(p)) ∧ " +
				"(∀p:num. exact_at(E.zero, D(p, 1), D(p, 0), v(p, 1), a(p))) ∧ " +
				"(∀p q:num. exact_at(V.zero, D(p, q + 2), D(p, q + 1), v(p, q + 2), v(p, q + 1))) ∧ " +
				"(∀p:num. ∀x:B. x ∈ D(p + 1, 0) ⇒ E.d(p + 1, a(p + 1, x)) = a(p, h(p + 1, 0, x)))",
		},
		Conclusion: "chain_map(R, «doubleTotal», E, double_edge(a)) ∧ " +
			"(∀n:num. " +
			"    module_isomorphism(R, " +
			"        homology_module(«doubleTotal», n), " +
			"        homology_module(E, n), " +
			"        homology_map(E, double_edge(a), n)))",
	},
		func(
			arg *Argument,
			double DoubleComplexFact[on.R, on.V],
			complexE ChainComplexFact[on.R],
			a *Arrow2[Nat, B, C],
			given Fact,
		) {
			s := arg.TermAs[Fun[Nat, A]]("alternating_sign")
			vModule := DoubleAmbientModule.Read(double)
			submodules := DoubleSubmodules.Read(double)
			hLinear, vLinear := DoubleHorizontalHom.Read(double), DoubleVerticalHom.Read(double)
			hyps := arg.Conjuncts(
				given,
				"a(p) is linear from D(p, 0) to E.terms(p)",
				"a(p) is onto E.terms(p)",
				"the augmented column is exact at D(p, 0)",
				"the columns are exact above the bottom row",
				"a carries the horizontal boundary to the boundary of E")
			aLinear, aOnto, aExact, columnsExact, aSquare := hyps[0], hyps[1], hyps[2], hyps[3], hyps[4]
			complexT := arg.Have(
				"the total complex is a complex",
				"chain_complex(R, «doubleTotal»)",
				By(DoubleTotalComplex.Read(double)))
			eBoundaryMaps := ComplexBoundaryHom.Read(complexE)
			additive := module.AddGroupOn.Read(vModule)
			signFacts := arg.Have(
				"every sign is a scalar whose square is one",
				"∀k:num. alternating_sign(k) ∈ R.carrier ∧ alternating_sign(k) * alternating_sign(k) = R.one",
				By(
					comm_ring.AlternatingSignIn.Read(module.RingOn.Read(vModule)),
					comm_ring.AlternatingSignSquare.Read(module.RingOn.Read(vModule))))

			// The top of a diagonal, the coordinate members at the heights 0
			// and 1, n + 0 read as n and 0 + 1 as 1: a total term of degree n
			// holds its coordinate n in D(n, 0), one of degree n + 1 its
			// coordinate n in D(n, 1), and at the coordinate n the boundary
			// out of degree n + 1 is h(n + 1, 0) on u(n + 1) plus
			// (−1)^n • v(n, 1) on u(n).
			V, D := arg.TermAs[ModuleOps[A, B]]("V"), arg.TermAs[Fun2[Nat, Nat, Set[B]]]("D")
			h, v := arg.TermAs[Fun3[Nat, Nat, B, B]]("h"), arg.TermAs[Fun3[Nat, Nat, B, B]]("v")
			zero, one := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
			top := func(b *Argument, n *Expr[Nat], u Typed[Fun[Nat, B]]) Fact {
				return b.Simplified(DoubleTotalCoordinate.At(V, D, n, zero, u), Fwd(nat_arith.AddZero))
			}
			belowTop := func(
				n *Expr[Nat],
				u Typed[Fun[Nat, B]],
			) Fact {
				return DoubleTotalCoordinate.At(V, D, n, one, u)
			}
			boundaryTop := func(b *Argument, n *Expr[Nat], u Typed[Fun[Nat, B]]) Fact {
				return b.Simplified(
					DoubleBoundaryCoordinate.At(V, h, v, s, n, zero, u),
					Fwd(nat_arith.AddZero),
					Fwd(nat_arith.AddLeftZeroClause))
			}

			// The edge is a chain map.
			edgeLinear := arg.Have(
				"each degree map u ↦ a(n)(u(n)) is linear",
				"∀n:num. "+
					"    module_homomorphism(R, "+
					"        complex_module(«doubleTotal», n), "+
					"        complex_module(E, n), "+
					"        double_edge(a, n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					aAtN := b.Have(
						"a(n) is linear",
						"module_homomorphism(R, restrict_module(V, D(n, 0)), complex_module(E, n), a(n))",
						By(aLinear))
					into := b.Have(
						"the edge of a diagonal lies in E.terms(n)",
						"∀u:(num → B). u ∈ double_total_terms(V, D, n) ⇒ double_edge(a, n, u) ∈ E.terms(n)",
						Derive(func(c *Argument) {
							u := c.FixAs[Fun[Nat, B]]("u")
							uTop := c.Have(
								"u(n) lies in D(n, 0)",
								"u(n) ∈ D(n, 0)",
								By(top(c, n, u), c.Assume()))
							c.Show(
								"a(n) carries it into E.terms(n)",
								Simp(Fwd(DoubleEdgeDef)),
								ByChase(Depth(0), aAtN, uTop))
						}))
					adds := b.Have(
						"the edge of a sum is the sum of the edges",
						Statement{
							Binders: "∀u w:(num → B).",
							Hypotheses: []string{
								"u ∈ double_total_terms(V, D, n)",
								"w ∈ double_total_terms(V, D, n)",
							},
							Conclusion: "double_edge(a, n, λp:num. V.add(u(p), w(p))) = " +
								"E.add(double_edge(a, n, u), double_edge(a, n, w))",
						},
						Derive(func(c *Argument) {
							u, w := c.FixAs[Fun[Nat, B]]("u"), c.FixAs[Fun[Nat, B]]("w")
							terms := c.Conjuncts(
								c.Assume(),
								"u is a diagonal of degree n",
								"w is a diagonal of degree n")
							c.Show(
								"a(n) is additive",
								Simp(Fwd(DoubleEdgeDef)),
								ByChase(Depth(0), aAtN, top(c, n, u), terms[0], top(c, n, w), terms[1]))
						}))
					scales := b.Have(
						"the edge of a scaled diagonal is the scaled edge",
						Statement{
							Binders: "∀c:A. ∀u:(num → B).",
							Hypotheses: []string{
								"c ∈ R.carrier",
								"u ∈ double_total_terms(V, D, n)",
							},
							Conclusion: "double_edge(a, n, λp:num. V.smul(c, u(p))) = E.smul(c, double_edge(a, n, u))",
						},
						Derive(func(c *Argument) {
							c.FixAs[A]("c")
							u := c.FixAs[Fun[Nat, B]]("u")
							scaled := c.Conjuncts(
								c.Assume(),
								"c is a scalar",
								"u is a diagonal of degree n")
							c.Show(
								"a(n) commutes with scaling",
								Simp(Fwd(DoubleEdgeDef)),
								By(module_homomorphism.HomSmul.Read(aAtN), scaled[0], top(c, n, u), scaled[1]))
						}))
					b.Show(
						"so it is a homomorphism of the degree modules",
						By(
							module_homomorphism.ModuleHomomorphismDef,
							ComplexModules.Read(complexT),
							ComplexModules.Read(complexE),
							into,
							adds,
							scales))
				}))
			edgeSquare := arg.Have(
				"the edge commutes with the boundaries: a(n) kills "+
					"the vertical part of the boundary's top coordinate",
				Statement{
					Binders: "∀n:num. ∀u:(num → B).",
					Hypotheses: []string{
						"u ∈ double_total_terms(V, D, n + 1)",
					},
					Conclusion: "double_edge(a, n, double_boundary(V, h, v, alternating_sign, n + 1, u)) = " +
						"E.d(n + 1, double_edge(a, n + 1, u))",
				},
				Derive(func(b *Argument) {
					n, u := b.FixAs[Nat]("n"), b.FixAs[Fun[Nat, B]]("u")
					uIn := b.Assume()
					uNext := b.Have(
						"u(n) lies in D(n, 1)",
						"u(n) ∈ D(n, 1)",
						By(belowTop(n, u), uIn))
					sign := b.Have(
						"alternating_sign(n) is a scalar",
						"alternating_sign(n) ∈ R.carrier",
						By(signFacts.At(n)))
					vAtN := b.Have(
						"v(n, 1) is linear",
						"module_homomorphism(R, restrict_module(V, D(n, 1)), restrict_module(V, D(n, 0)), v(n, 1))",
						By(vLinear.At(n, zero), nat_arith.AddLeftZeroClause))
					scaledIn := b.Have(
						"alternating_sign(n) • u(n) lies in D(n, 1)",
						"alternating_sign(n) • u(n) ∈ D(n, 1)",
						By(submodule.SubmoduleSmul, submodules, sign, uNext))
					vScales := b.Have(
						"v(n, 1) commutes with the scaling by alternating_sign(n)",
						"v(n, 1, alternating_sign(n) • u(n)) = alternating_sign(n) • v(n, 1, u(n))",
						By(module_homomorphism.HomSmul.Read(vAtN), sign, uNext))
					topCoordinate := boundaryTop(b, n, u)
					b.Show(
						"a(n) kills alternating_sign(n) • v(n, 1)(u(n)) and carries "+
							"h(n + 1, 0)(u(n + 1)) to E.d(n + 1)(a(n + 1)(u(n + 1)))",
						Simp(Fwd(DoubleEdgeDef)),
						topCoordinate.Rw(),
						ByChase(
							Depth(0),
							aLinear,
							hLinear,
							vAtN,
							aExact,
							aSquare,
							top(b, b.TermAs[Nat]("n + 1"), u),
							uIn,
							uNext,
							sign,
							scaledIn,
							vScales))
				}))
			chainMap := arg.Have(
				"so the edge is a chain map",
				"chain_map(R, «doubleTotal», E, double_edge(a))",
				By(ChainMapDef, edgeLinear, edgeSquare))

			// One-to-one on homology: subtracting the boundary of the diagonal z
			// leaves a cycle that vanishes from the coordinate n on.
			reflects := arg.Have(
				"a total cycle whose edge is a boundary of E is a boundary",
				Statement{
					Binders: "∀n:num. ∀u:(num → B).",
					Hypotheses: []string{
						"u ∈ cycles(«doubleTotal», n)",
						"double_edge(a, n, u) ∈ boundaries(E, n)",
					},
					Conclusion: "u ∈ boundaries(«doubleTotal», n)",
				},
				Derive(func(b *Argument) {
					n, u := b.FixAs[Nat]("n"), b.FixAs[Fun[Nat, B]]("u")
					cycleEdge := b.Conjuncts(
						b.Assume(),
						"u is a total cycle",
						"its edge is a boundary of E")
					uIn := b.Have(
						"u is a diagonal of degree n",
						"u ∈ double_total_terms(V, D, n)",
						BySets(b.Unfolded(cycleEdge[0], CyclesDef)))
					uTop := b.Have(
						"u(n) lies in D(n, 0)",
						"u(n) ∈ D(n, 0)",
						By(top(b, n, u), uIn))
					edgeImage := b.Simplified(b.Unfolded(cycleEdge[1], BoundariesDef), Fwd(DoubleEdgeDef))
					_, eIs := b.ObtainAs[C](
						"a(n)(u(n)) is E.d(n + 1)(e) for an e of E.terms(n + 1)",
						"∃e:C. a(n, u(n)) = E.d(n + 1, e) ∧ e ∈ E.terms(n + 1)",
						By(edgeImage, set_basic.InImage))
					_, xIs := b.ObtainAs[B](
						"e is a(n + 1)(x) for an x of D(n + 1, 0), a(n + 1) being onto",
						"∃x:B. x ∈ D(n + 1, 0) ∧ a(n + 1, x) = e",
						ByChase(Depth(1), aLinear, aOnto, eIs))
					lift := b.Conjuncts(
						xIs,
						"x lies in D(n + 1, 0)",
						"a(n + 1)(x) = e")
					hAtN := b.Have(
						"h(n + 1, 0) is linear",
						"module_homomorphism(R, restrict_module(V, D(n + 1, 0)), restrict_module(V, D(n, 0)), h(n + 1, 0))",
						By(hLinear))
					vAtN := b.Have(
						"v(n, 1) is linear",
						"module_homomorphism(R, restrict_module(V, D(n, 1)), restrict_module(V, D(n, 0)), v(n, 1))",
						By(vLinear.At(n, zero), nat_arith.AddLeftZeroClause))
					_, yIs := b.ObtainAs[B](
						"the square gives a(n)(u(n)) = a(n)(h(n + 1, 0)(x)), so the "+
							"augmented exactness writes u(n) − h(n + 1, 0)(x) as v(n, 1)(y)",
						"∃y:B. y ∈ D(n, 1) ∧ v(n, 1, y) = V.add(u(n), V.neg(h(n + 1, 0, x)))",
						ByChase(Depth(1), aLinear, hAtN, vAtN, aExact, aSquare, lift[0], eBoundaryMaps, uTop, eIs, xIs))
					preimage := b.Conjuncts(
						yIs,
						"y lies in D(n, 1)",
						"v(n, 1)(y) = u(n) − h(n + 1, 0)(x)")
					zTerm, zDef := b.LetAs[Fun[Nat, B]](
						"z", "λp:num. COND(p = n + 1, x, COND(p = n, alternating_sign(n) • y, V.zero))")
					notTop := b.Have(
						"n is not n + 1",
						"¬(n = n + 1)",
						ByArith())
					zAtTop := b.Have(
						"z holds x at n + 1",
						"z(n + 1) = x",
						By(zDef))
					zAtN := b.Have(
						"z holds alternating_sign(n) • y at n",
						"z(n) = alternating_sign(n) • y",
						By(zDef, notTop))
					zElsewhere := b.Have(
						"z is zero at every other coordinate",
						"∀p:num. ¬(p = n + 1) ∧ ¬(p = n) ⇒ z(p) = V.zero",
						By(zDef))
					sign := b.Have(
						"alternating_sign(n) is a scalar squaring to one",
						"alternating_sign(n) ∈ R.carrier ∧ alternating_sign(n) * alternating_sign(n) = R.one",
						By(signFacts.At(n)))
					signParts := b.Conjuncts(
						sign,
						"alternating_sign(n) is a scalar",
						"the sign at n squares to one")
					scaledIn := b.Have(
						"alternating_sign(n) • y lies in D(n, 1)",
						"alternating_sign(n) • y ∈ D(n, 1)",
						By(submodule.SubmoduleSmul, submodules, signParts[0], preimage[0]))
					zIn := b.Have(
						"z is a diagonal of degree n + 1",
						"z ∈ double_total_terms(V, D, n + 1)",
						Derive(func(c *Argument) {
							low := c.Have(
								"its coordinates up to n + 1 lie in their terms",
								"∀p:num. p ≤ n + 1 ⇒ z(p) ∈ D(p, n + 1 - p)",
								Derive(func(d *Argument) {
									p := d.FixAs[Nat]("p")
									d.Assume()
									d.Cases(d.Term("p = n + 1"))
									d.When(
										"at n + 1 the coordinate is x",
										func(e *Argument, isTop Fact) {
											degree := e.Have(
												"n + 1 − (n + 1) = 0",
												"n + 1 - (n + 1) = 0",
												ByArith())
											e.Show(
												"x lies in D(n + 1, 0)",
												isTop.Rw(),
												zAtTop.Rw(),
												By(degree, lift[0]))
										})
									d.Otherwise(
										"below n + 1",
										func(e *Argument, notTopP Fact) {
											e.Cases(e.Term("p = n"))
											e.When(
												"at n the coordinate is alternating_sign(n) • y",
												func(g *Argument, isN Fact) {
													degree := g.Have(
														"n + 1 − n = 1",
														"n + 1 - n = 1",
														ByArith())
													g.Show(
														"alternating_sign(n) • y lies in D(n, 1)",
														isN.Rw(),
														zAtN.Rw(),
														By(degree, scaledIn))
												})
											e.Otherwise(
												"elsewhere the coordinate is zero",
												func(g *Argument, notN Fact) {
													zZero := g.Have(
														"z(p) is zero",
														"z(p) = V.zero",
														By(zElsewhere.At(p), notTopP, notN))
													g.Show(
														"zero lies in the submodule D(p, n + 1 − p)",
														zZero.Rw(),
														By(submodule.SubmoduleZero, submodules.At(p, g.TermAs[Nat]("n + 1 - p"))))
												})
										})
								}))
							high := c.Have(
								"past n + 1 they vanish",
								"∀p:num. n + 1 < p ⇒ z(p) = V.zero",
								Derive(func(d *Argument) {
									p := d.FixAs[Nat]("p")
									above := d.Assume()
									degree := d.Have(
										"p is neither n + 1 nor n",
										"¬(p = n + 1) ∧ ¬(p = n)",
										ByArith(above))
									d.Show(
										"so the coordinate is zero",
										By(zElsewhere.At(p), degree))
								}))
							c.Show(
								"so z is a diagonal of degree n + 1",
								By(DoubleTotalTermsMember.At(V, D, c.TermAs[Nat]("n + 1"), zTerm), low, high))
						}))
					vScales := b.Have(
						"v(n, 1) commutes with the scaling by alternating_sign(n)",
						"v(n, 1, alternating_sign(n) • y) = alternating_sign(n) • v(n, 1, y)",
						By(module_homomorphism.HomSmul.Read(vAtN), signParts[0], preimage[0]))
					vyIn := b.Have(
						"v(n, 1)(y) lies in D(n, 0)",
						"v(n, 1, y) ∈ D(n, 0)",
						ByChase(Depth(0), vAtN, preimage[0]))
					targetModule := b.Have(
						"D(n, 0) is a module",
						"module_on(R, restrict_module(V, D(n, 0)))",
						By(module_homomorphism.HomTarget, vAtN))
					signMember := proof.MemberOf(b.TermAs[A]("alternating_sign(n)"), signParts[0])
					vyMember := proof.MemberOf(b.TermAs[B]("v(n, 1, y)"), vyIn)
					zBoundary := boundaryTop(b, n, zTerm)
					zTop := b.Have(
						"the boundary of z at the coordinate n is u(n)",
						"double_boundary(V, h, v, alternating_sign, n + 1, z, n) = u(n)",
						CalcEq(
							Leg(
								b.TermAs[B]("V.add(h(n + 1, 0, x), V.smul(alternating_sign(n), v(n, 1, alternating_sign(n) • y)))"),
								"z holds x at n + 1 and alternating_sign(n) • y at n",
								zBoundary.Rw(),
								zAtTop.Rw(),
								zAtN.Rw(),
								Basic()),
							Leg(
								b.TermAs[B]("V.add(h(n + 1, 0, x), V.smul(alternating_sign(n) * alternating_sign(n), v(n, 1, y)))"),
								"v(n, 1) commutes with alternating_sign(n), and scaling twice is scaling by the product",
								vScales.Rw(),
								By(module.SmulMul.Read(targetModule).At(signMember, signMember, vyMember))),
							Leg(
								b.TermAs[B]("V.add(h(n + 1, 0, x), v(n, 1, y))"),
								"the sign at n squares to one",
								signParts[1].Rw(),
								By(module.SmulOne.Read(targetModule).At(vyMember))),
							FinalLeg(
								"v(n, 1)(y) = u(n) − h(n + 1, 0)(x)",
								ByChase(Depth(0), hAtN, vAtN, uTop, lift[0], preimage[0], preimage[1])),
						))
					corrected := b.Have(
						"u − ∂z is a cycle, and a boundary only if u is one",
						"(λp:num. V.add(u(p), V.neg(double_boundary(V, h, v, alternating_sign, n + 1, z, p)))) ∈ "+
							"cycles(«doubleTotal», n) ∧ "+
							"((λp:num. V.add(u(p), V.neg(double_boundary(V, h, v, alternating_sign, n + 1, z, p)))) ∈ "+
							"    boundaries(«doubleTotal», n) ⇒ "+
							"    u ∈ boundaries(«doubleTotal», n))",
						By(
							At(CycleCorrection, b.Term("R"), b.Term("«doubleTotal»"), n, u, zTerm),
							complexT,
							cycleEdge[0],
							zIn))
					vanishes := b.Have(
						"u − ∂z vanishes from the coordinate n on",
						Statement{
							Binders: "∀p:num.",
							Hypotheses: []string{
								"n ≤ p",
							},
							Conclusion: "V.add(u(p), V.neg(double_boundary(V, h, v, alternating_sign, n + 1, z, p))) = V.zero",
						},
						Derive(func(c *Argument) {
							p := c.FixAs[Nat]("p")
							atLeast := c.Assume()
							c.Cases(c.Term("p = n"))
							c.When(
								"at n the boundary of z is u(n)",
								func(d *Argument, isN Fact) {
									d.Show(
										"u(n) − u(n) = 0",
										isN.Rw(),
										zTop.Rw(),
										ByChase(Depth(0), targetModule, uTop))
								})
							c.Otherwise(
								"past n both vanish",
								func(d *Argument, notN Fact) {
									past := d.Have(
										"n < p",
										"n < p",
										ByArith(notN, atLeast))
									uZero := d.Have(
										"u(p) is zero",
										"u(p) = V.zero",
										By(DoubleTotalPast.At(V, D, n, p, u), uIn, past))
									zZero := d.Have(
										"the boundary of z is zero there",
										"double_boundary(V, h, v, alternating_sign, n + 1, z, p) = V.zero",
										By(DoubleBoundaryPast.At(V, h, v, s, n, p, zTerm), past))
									d.Show(
										"0 − 0 = 0",
										uZero.Rw(),
										zZero.Rw(),
										By(group.RightInverseOn.Read(additive), group.OneIn.Read(additive)))
								})
						}))
					correctedParts := b.Conjuncts(
						corrected,
						"u − ∂z is a cycle",
						"if u − ∂z is a boundary so is u")
					degree := b.Have(
						"n ≤ n",
						"n ≤ n",
						ByArith())
					boundary := b.Have(
						"so u − ∂z is a boundary",
						"(λp:num. V.add(u(p), V.neg(double_boundary(V, h, v, alternating_sign, n + 1, z, p)))) ∈ "+
							"boundaries(«doubleTotal», n)",
						By(
							At(
								ColumnCycleVanishing,
								b.Term("R"),
								b.Term("V"),
								b.Term("D"),
								b.Term("h"),
								b.Term("v"),
								n,
								n,
								b.Term("λp:num. V.add(u(p), V.neg(double_boundary(V, h, v, alternating_sign, n + 1, z, p)))")),
							double,
							columnsExact,
							degree,
							correctedParts[0],
							vanishes))
					b.Show(
						"and so u is a boundary",
						By(correctedParts[1], boundary))
				}))

			lift := At(
				AugmentedCycleLift,
				arg.Term("R"),
				arg.Term("V"),
				arg.Term("D"),
				arg.Term("h"),
				arg.Term("v"),
				arg.Term("E"),
				a)
			lifts := arg.Have(
				"every cycle of E is the edge of a total cycle",
				Statement{
					Binders: "∀n:num. ∀e:C.",
					Hypotheses: []string{
						"e ∈ cycles(E, n)",
					},
					Conclusion: "∃u:(num → B). u ∈ cycles(«doubleTotal», n) ∧ double_edge(a, n, u) = e",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.FixAs[C]("e")
					cycle := b.Assume()
					u, uIs := b.ObtainAs[Fun[Nat, B]](
						"a cycle u of the total complex with a(n)(u(n)) = e",
						"∃u:(num → B). u ∈ cycles(«doubleTotal», n) ∧ a(n, u(n)) = e",
						By(lift, double, complexE, given, cycle))
					b.Take(u)
					b.Show(
						"its edge is e",
						Simp(Fwd(DoubleEdgeDef)),
						By(uIs))
				}))
			isomorphisms := arg.Have(
				"so the edge is an isomorphism on homology in every degree",
				"∀n:num. "+
					"    module_isomorphism(R, "+
					"        homology_module(«doubleTotal», n), "+
					"        homology_module(E, n), "+
					"        homology_map(E, double_edge(a), n))",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(
						At(
							HomologyIsomorphismCriterion,
							arg.Term("R"),
							arg.Term("«doubleTotal»"),
							arg.Term("E"),
							arg.Term("double_edge(a)"),
							n),
						complexT,
						complexE,
						chainMap,
						lifts.At(n),
						reflects.At(n))
				}))
			arg.Show(
				"the edge is a chain map and an isomorphism on homology",
				By(chainMap, isomorphisms))
		}),
})}

// ---------------------------------------------------------------------------
// The transpose: assembly along the columns
// ---------------------------------------------------------------------------

// TransposeDoubleComplex — the transpose of a double complex is a double
// complex: the terms D(q, p) at (p, q), with v as the horizontal boundary
// and h as the vertical one.
var TransposeDoubleComplex = transposeDoubleComplexThm{family.Add(registry.ProofEntry{
	Name: "TransposeDoubleComplex",
	Key:  "prop_d10cf4f00e59612f",
	Deps: []registry.EntryLike{DoubleComplex},
	Build: family.Card(
		DoubleComplex.Statement(
			"double_complex(R, "+
				"    V, "+
				"    (λp:num. λq:num. D(q, p)), "+
				"    (λp:num. λq:num. v(q, p)), "+
				"    (λp:num. λq:num. h(q, p)))"),
		"Unfold double_complex at both and read each conjunct of the transpose at (q, p): the "+
			"submodules and the two families of homomorphisms trade places, the two squares-to-zero "+
			"trade places, and the commuting square at (q + 1, p + 1) is the original one."),
})}

// TransposeTotalIsomorphic — the total complex of a double complex and of
// its transpose are isomorphic by the sign alternating_sign(p·q) =
// (−1)^(pq) on the (p, q) coordinate: u goes to the diagonal whose
// coordinate q ≤ n is (−1)^((n − q)·q) • u(n − q).
var TransposeTotalIsomorphic = transposeTotalIsomorphicThm{family.Add(registry.ProofEntry{
	Name: "TransposeTotalIsomorphic",
	Key:  "prop_e40b093194b81e28",
	Deps: []registry.EntryLike{
		TransposeDoubleComplex,
		DoubleTotalComplex,
		DoubleTotalDef,
		DoubleTotalTermsMember,
		DoubleTotalCoordinate,
		DoubleTotalPast,
		DoubleBoundaryCoordinate,
		DoubleBoundaryPast,
		ChainIsomorphismDef,
		ChainMapDef,
		module_homomorphism.HomSmul,
		module_homomorphism.HomAdd,
		module_homomorphism.ModuleIsomorphismDef,
		module.SmulMul,
		module.SmulAddRight,
		module.SmulOne,
		comm_ring.AlternatingSignAdd,
		comm_ring.AlternatingSignSquare,
	},
	Build: family.Card(
		DoubleComplex.Statement(
			"chain_isomorphism(R, "+
				"    «doubleTotal», "+
				"    double_total(V, "+
				"        λp:num. λq:num. D(q, p), "+
				"        λp:num. λq:num. v(q, p), "+
				"        λp:num. λq:num. h(q, p), "+
				"        alternating_sign), "+
				"    λn:num. λu:(num → B). λq:num. "+
				"        COND(q ≤ n, V.smul(alternating_sign((n - q) * q), u(n - q)), V.zero))"),
		"Write σ(p, q) = alternating_sign(p·q). On the coordinate (p, q) of a diagonal of degree "+
			"n − 1 the original boundary gives σ(p, q) • (h(u_{p+1}) + alternating_sign(p) • v(u_p)), "+
			"the transposed one σ(p, q + 1) • v(u_p) + alternating_sign(q) σ(p + 1, q) • h(u_{p+1}); "+
			"they agree because alternating_sign(p) σ(p, q) = σ(p, q + 1) by the exponent law "+
			"(AlternatingSignAdd), and alternating_sign(q) σ(p + 1, q) = σ(p, q) by the exponent law "+
			"and the sign alternating_sign(q) squaring to R.one (AlternatingSignSquare). Each degree "+
			"map is linear, the scalars commuting, and its own inverse up to the transpose, every "+
			"sign squaring to R.one (Weibel 1.2.5 for the sign trick)."),
	Reading: "The sign is load-bearing: the original total boundary puts " +
		"alternating_sign(p) on v and none on h, the transposed one alternating_sign(q) on h " +
		"and none on v, so the identity on coordinates is a chain map only where those signed " +
		"parts vanish. Coordinates past n are zero on both sides, and at q = n the coordinate " +
		"is alternating_sign(0) • u(0) = u(0). Linearity of the sign map uses that R is " +
		"commutative; in characteristic 2 every sign is R.one and the map is plain reindexing.",
})}

// AcyclicAssemblyColumns — a double complex whose columns are exact,
// including the vertical boundary onto D(p, 0), has an exact total
// complex.
var AcyclicAssemblyColumns = acyclicAssemblyColumnsThm{family.Add(registry.ProofEntry{
	Name: "AcyclicAssemblyColumns",
	Key:  "prop_5fa7c0c65b17060d",
	Reading: "image(v(p, 1), D(p, 1)) = D(p, 0) is load-bearing: a double complex " +
		"with one nonzero module, at (0, 0), has exact columns above the bottom row, " +
		"yet its total complex is that module in degree 0 with the zero boundary into it.",
	Deps: []registry.EntryLike{
		TransposeDoubleComplex,
		TransposeTotalIsomorphic,
		AcyclicAssembly,
		DoubleTotalComplex,
		ChainIsomorphismQuasiIsomorphism,
		QuasiIsomorphismAcyclic,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"∀p q:num. exact_at(V.zero, D(p, q + 2), D(p, q + 1), v(p, q + 2), v(p, q + 1))",
			"∀p:num. image(v(p, 1), D(p, 1)) = D(p, 0)",
		},
		Conclusion: "cycles(«doubleTotal», n) = boundaries(«doubleTotal», n)",
	}),
		"The columns of D are the rows of its transpose (TransposeDoubleComplex), so "+
			"AcyclicAssembly makes the transpose's total complex exact. TransposeTotalIsomorphic joins "+
			"the two total complexes (DoubleTotalComplex) by a chain isomorphism, a quasi-isomorphism "+
			"(ChainIsomorphismQuasiIsomorphism), and QuasiIsomorphismAcyclic carries the exactness back."),
})}

// AugmentedAssemblyRows — a double complex whose rows, augmented at
// p = −1 by maps b(q) from D(0, q) onto a complex E commuting with the
// vertical boundary, are exact maps by u ↦ b(n)(u(0)) quasi-isomorphically
// onto E.
var AugmentedAssemblyRows = augmentedAssemblyRowsThm{family.Add(registry.ProofEntry{
	Name: "AugmentedAssemblyRows",
	Key:  "prop_358e4f89a20eb3c8",
	Deps: []registry.EntryLike{
		TransposeDoubleComplex,
		TransposeTotalIsomorphic,
		AugmentedAssembly,
		DoubleTotalComplex,
		DoubleEdgeDef,
		ChainIsomorphismQuasiIsomorphism,
		QuasiIsomorphismCompose,
		QuasiIsomorphismDef,
		module.SmulOne,
		ChainMapDef,
		DoubleTotalDef,
		DoubleBoundaryDef,
		comm_ring.AlternatingSignDef,
		HomologyMapCoset,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀E:complex_ops(A, C). ∀b:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, E)",
			"∀q:num. module_homomorphism(R, restrict_module(V, D(0, q)), complex_module(E, q), b(q))",
			"∀q:num. image(b(q), D(0, q)) = E.terms(q)",
			"∀q:num. exact_at(E.zero, D(1, q), D(0, q), h(1, q), b(q))",
			"∀p q:num. exact_at(V.zero, D(p + 2, q), D(p + 1, q), h(p + 2, q), h(p + 1, q))",
			"∀q:num. ∀x:B. x ∈ D(0, q + 1) ⇒ E.d(q + 1)(b(q + 1)(x)) = b(q)(v(0, q + 1, x))",
		},
		Conclusion: "quasi_isomorphism(R, «doubleTotal», E, λn:num. λu:(num → B). b(n)(u(0)))",
	}),
		"In the transpose the augmented rows are augmented columns, b(q) on the edge D^T(q, 0) = "+
			"D(0, q) commuting with the transposed horizontal boundary v(0, ·), so AugmentedAssembly "+
			"makes double_edge(b) a quasi-isomorphism from the transpose's total complex onto E; "+
			"preceded by TransposeTotalIsomorphic (ChainIsomorphismQuasiIsomorphism, "+
			"QuasiIsomorphismCompose) it gives the quasi-isomorphism u ↦ b(n)(alternating_sign(0) • "+
			"u(0)) = b(n)(R.one • u(0)) (AlternatingSignDef), equal to u ↦ b(n)(u(0)) only on the total "+
			"terms (SmulOne). So prove chain_map for u ↦ b(n)(u(0)) directly (ChainMapDef): it is linear "+
			"into E.terms(n), and coordinate 0 of the total boundary out of n + 1 is h(1, n)(u(1)) + "+
			"R.one • v(0, n + 1)(u(0)) (DoubleTotalDef, DoubleBoundaryDef, AlternatingSignDef), whose "+
			"first term b(n) kills by exactness at D(0, n) (ExactAtDef) and whose second it carries to "+
			"E.d(n + 1)(b(n + 1)(u(0))) by linearity and the commuting square. By HomologyMapCoset both "+
			"maps send the class of a cycle u to the class of b(n)(u(0)), so their homology maps agree "+
			"on the carrier, and module_isomorphism carries over (ModuleIsomorphismDef)."),
	Reading: "The hypotheses are AugmentedAssembly's read along the rows: b(q) " +
		"is the augmentation of row q at p = −1, exactness at D(0, q) is ker b(q) = " +
		"image h(1, q), and b(q) is onto E.terms(q). The commuting square carries " +
		"no sign because alternating_sign(0) = R.one is the sign on the column p = 0.",
})}

// ---------------------------------------------------------------------------
// Columns and maps of double complexes
// ---------------------------------------------------------------------------

// DoubleColumnDef — `double_column(V, D, v, p)`: the column p of a double
// complex as a complex, D(p, q) in degree q with the vertical boundary
// v(p, q) and the operations of V.
var DoubleColumnDef = doubleColumnDefThm{family.Define(registry.DefEntry{
	Name: "DoubleColumnDef", Const: "double_column",
	Key: "prop_2b3d7081b0309f86",
	Type: "module_ops(A, B) → " +
		"(num → num → set(B)) → " +
		"(num → num → B → B) → " +
		"num → " +
		"complex_ops(A, B)",
	Equations: []string{
		"∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀v:(num → num → B → B). ∀p:num. " +
			"    double_column(V, D, v, p) = " +
			"    pack_complex(V.add, V.zero, V.neg, V.smul, (λq:num. D(p, q)), (λq:num. v(p, q)))",
	},
	Deps: []registry.EntryLike{ComplexAddDef},
})}

// DoubleComplexMapDef — `double_complex_map(R, V, D, h, v, V', D', h',
// v', F)`: each F(p, q) is a homomorphism from D(p, q) to D'(p, q), and F
// commutes with the horizontal and with the vertical boundaries.
var DoubleComplexMapDef = doubleComplexMapDefThm{family.Define(registry.DefEntry{
	Name: "DoubleComplexMapDef", Const: "double_complex_map",
	Key: "prop_af3b17791f357b49",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"(num → num → set(B)) → " +
		"(num → num → B → B) → " +
		"(num → num → B → B) → " +
		"module_ops(A, C) → " +
		"(num → num → set(C)) → " +
		"(num → num → C → C) → " +
		"(num → num → C → C) → " +
		"(num → num → B → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀D:(num → num → set(B)). " +
			"∀h v:(num → num → B → B). " +
			"∀V':module_ops(A, C). " +
			"∀D':(num → num → set(C)). " +
			"∀h' v':(num → num → C → C). " +
			"∀F:(num → num → B → C). " +
			"    double_complex_map(R, V, D, h, v, V', D', h', v', F) ⇔ " +
			"    (∀p q:num. " +
			"        module_homomorphism(R, " +
			"            restrict_module(V, D(p, q)), " +
			"            restrict_module(V', D'(p, q)), " +
			"            F(p, q))) ∧ " +
			"    (∀p q:num. ∀x:B. " +
			"        x ∈ D(p + 1, q) ⇒ F(p, q, h(p + 1, q, x)) = h'(p + 1, q, F(p + 1, q, x))) ∧ " +
			"    (∀p q:num. ∀x:B. x ∈ D(p, q + 1) ⇒ F(p, q, v(p, q + 1, x)) = v'(p, q + 1, F(p, q + 1, x)))",
	},
})}

// DoubleTotalMapDef — `double_total_map(F)`: a map of double complexes
// read on the total complexes, F(p, n − p) on the coordinate p of a
// diagonal of degree n.
var DoubleTotalMapDef = doubleTotalMapDefThm{family.Define(registry.DefEntry{
	Name: "DoubleTotalMapDef", Const: "double_total_map",
	Key:  "prop_2001f330120d616e",
	Type: "(num → num → B → C) → num → (num → B) → num → C",
	Equations: []string{
		"∀F:(num → num → B → C). ∀n:num. ∀u:(num → B). ∀p:num. " +
			"    double_total_map(F, n, u, p) = F(p, n - p, u(p))",
	},
})}

// DoubleColumnChainComplex — every column of a double complex is a
// complex.
var DoubleColumnChainComplex = doubleColumnChainComplexThm{family.Add(registry.ProofEntry{
	Name: "DoubleColumnChainComplex",
	Key:  "prop_64b2d04b6a1cdbbc",
	Deps: []registry.EntryLike{
		DoubleColumnDef,
		DoubleComplex,
		ChainComplex,
		submodule.SubmoduleModuleOn,
	},
	Build: family.Card(DoubleComplex.Statement("∀p:num. chain_complex(R, double_column(V, D, v, p))"),
		"Each degree D(p, q) is a submodule of V, so a module (SubmoduleModuleOn); "+
			"the boundaries are the vertical homomorphisms v(p, q + 1), and two in a "+
			"row vanish by the vertical square-to-zero of double_complex."),
})}

// DoubleComplexMapTotal — a map of double complexes is a chain map of the
// total complexes.
var DoubleComplexMapTotal = doubleComplexMapTotalThm{family.Add(registry.ProofEntry{
	Name: "DoubleComplexMapTotal",
	Key:  "prop_1af5bf3c078579a4",
	Reading: "Past the diagonal the degree map reads F(p, 0)(V.zero), the " +
		"subtraction n − p being truncated, and the map's linearity makes it V'.zero.",
	Deps: []registry.EntryLike{
		DoubleComplexMapDef,
		DoubleTotalMapDef,
		DoubleTotalDef,
		DoubleTotalTermsMember,
		DoubleTotalCoordinate,
		DoubleTotalPast,
		DoubleBoundaryCoordinate,
		DoubleBoundaryPast,
		DoubleTotalComplex,
		ChainMapDef,
		module_homomorphism.HomAdd,
		module_homomorphism.HomSmul,
		module_homomorphism.HomZero,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀V':module_ops(A, C). " +
			"∀D':(num → num → set(C)). " +
			"∀h' v':(num → num → C → C). " +
			"∀F:(num → num → B → C).",
		Hypotheses: []string{
			"double_complex(R, V', D', h', v')",
			"double_complex_map(R, V, D, h, v, V', D', h', v', F)",
		},
		Conclusion: "chain_map(R, " +
			"    «doubleTotal», " +
			"    double_total(V', D', h', v', alternating_sign), " +
			"    double_total_map(F))",
	}),
		"Coordinatewise F(p, n − p) is a homomorphism into D'(p, n − p), and past n it "+
			"sends V.zero to V'.zero (HomZero), so the degree map lands in the total degree "+
			"and is linear. On the coordinate p of the boundary, F(p, ·) of h(u_{p+1}) + "+
			"alternating_sign(p) • v(u_p) is h'(F(u_{p+1})) + alternating_sign(p) • v'(F(u_p)) "+
			"by the two commuting squares and linearity; both sides read the same signs."),
})}

// DoubleShortExactTotal — two maps of double complexes, short exact at
// every (p, q), give a short exact sequence of the total complexes.
var DoubleShortExactTotal = doubleShortExactTotalThm{family.Add(registry.ProofEntry{
	Name: "DoubleShortExactTotal",
	Key:  "prop_5b24a575398433eb",
	Deps: []registry.EntryLike{
		DoubleComplexMapTotal,
		DoubleTotalComplex,
		DoubleTotalMapDef,
		DoubleTotalTermsDef,
		ShortExactComplexes,
		ExactComplexesDef,
		module_homomorphism.ExactAtDef,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V':module_ops(A, B). " +
			"∀D':(num → num → set(B)). " +
			"∀h' v':(num → num → B → B). " +
			"∀V:module_ops(A, C). " +
			"∀D:(num → num → set(C)). " +
			"∀h v:(num → num → C → C). " +
			"∀V'':module_ops(A, E). " +
			"∀D'':(num → num → set(E)). " +
			"∀h'' v'':(num → num → E → E). " +
			"∀F:(num → num → B → C). " +
			"∀G:(num → num → C → E).",
		Hypotheses: []string{
			"double_complex(R, V', D', h', v')",
			"double_complex(R, V, D, h, v)",
			"double_complex(R, V'', D'', h'', v'')",
			"double_complex_map(R, V', D', h', v', V, D, h, v, F)",
			"double_complex_map(R, V, D, h, v, V'', D'', h'', v'', G)",
			"∀p q:num. " +
				"    injective_on(D'(p, q), F(p, q)) ∧ " +
				"    exact_at(V''.zero, D'(p, q), D(p, q), F(p, q), G(p, q)) ∧ " +
				"    image(G(p, q), D(p, q)) = D''(p, q)",
		},
		Conclusion: "short_exact_complexes(R, " +
			"    double_total(V', D', h', v', alternating_sign), " +
			"    «doubleTotal», " +
			"    double_total(V'', D'', h'', v'', alternating_sign), " +
			"    double_total_map(F), " +
			"    double_total_map(G))",
	},
		"The three total complexes are complexes (DoubleTotalComplex) and the two total maps chain maps "+
			"(DoubleComplexMapTotal). A degree of a total complex is a finite diagonal, so exactness is "+
			"coordinatewise: F is one-to-one on each coordinate, a diagonal killed by G has each coordinate "+
			"F of one in D', zero past n, and a diagonal of D'' lifts coordinate by coordinate, zero past n."),
})}

// ---------------------------------------------------------------------------
// The columnwise cone of a map of double complexes
// ---------------------------------------------------------------------------

// doubleConeTermsDef — `double_cone_terms(V, D, D')`: the terms of the
// columnwise cone of a map D → D', the pairs (x, y) with x in D(p, q − 1)
// — V.zero alone when q = 0 — and y in D'(p, q).
var doubleConeTermsDef = doubleConeTermsDefThm{family.Define(registry.DefEntry{
	Name: "doubleConeTermsDef", Const: "double_cone_terms",
	Key: "prop_d091d45ee63d7595",
	Type: "module_ops(A, B) → " +
		"(num → num → set(B)) → " +
		"(num → num → set(C)) → " +
		"num → " +
		"num → " +
		"set(prod(B, C))",
	Equations: []string{
		"∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀D':(num → num → set(C)). ∀p q:num. " +
			"    double_cone_terms(V, D, D', p, q) = set_cross(COND(q = 0, {V.zero}, D(p, q - 1)), D'(p, q))",
	},
})}

// doubleConeHorizontalDef — `double_cone_horizontal(h, h')`: the
// horizontal boundary of the columnwise cone, h on the first component one
// vertical degree down and h' on the second.
var doubleConeHorizontalDef = doubleConeHorizontalDefThm{family.Define(registry.DefEntry{
	Name: "doubleConeHorizontalDef", Const: "double_cone_horizontal",
	Key:  "prop_312eacc888a82eae",
	Type: "(num → num → B → B) → (num → num → C → C) → num → num → prod(B, C) → prod(B, C)",
	Equations: []string{
		"∀h:(num → num → B → B). ∀h':(num → num → C → C). ∀p q:num. ∀z:prod(B, C). " +
			"    double_cone_horizontal(h, h', p, q, z) = (h(p, q - 1, fst(z)), h'(p, q, snd(z)))",
	},
})}

// doubleConeVerticalDef — `double_cone_vertical(V, v, V', v', F)`: the
// vertical boundary of the columnwise cone, the boundary of chain_cone in
// each column: out of the vertical degree q it sends (x, y) to
// (−v(p, q − 1)(x), F(p, q − 1)(x) + v'(p, q)(y)), and to
// (V.zero, F(p, 0)(x) + v'(p, 1)(y)) out of q = 1.
var doubleConeVerticalDef = doubleConeVerticalDefThm{family.Define(registry.DefEntry{
	Name: "doubleConeVerticalDef", Const: "double_cone_vertical",
	Key: "prop_fcccbf458f625ca0",
	Type: "module_ops(A, B) → " +
		"(num → num → B → B) → " +
		"module_ops(A, C) → " +
		"(num → num → C → C) → " +
		"(num → num → B → C) → " +
		"num → " +
		"num → " +
		"prod(B, C) → " +
		"prod(B, C)",
	Equations: []string{
		"∀V:module_ops(A, B). " +
			"∀v:(num → num → B → B). " +
			"∀V':module_ops(A, C). " +
			"∀v':(num → num → C → C). " +
			"∀F:(num → num → B → C). " +
			"∀p q:num. " +
			"∀z:prod(B, C). " +
			"    double_cone_vertical(V, v, V', v', F, p, q, z) = " +
			"    (COND(q ≤ 1, V.zero, V.neg(v(p, q - 1, fst(z)))), " +
			"        V'.add(F(p, q - 1, fst(z)), v'(p, q, snd(z))))",
	},
})}

// DoubleConeDoubleComplex — the columnwise cone of a map of double
// complexes is a double complex at the pair type.
var DoubleConeDoubleComplex = doubleConeDoubleComplexThm{family.Add(registry.ProofEntry{
	Name: "DoubleConeDoubleComplex",
	Key:  "prop_76595d936e7911d",
	Deps: []registry.EntryLike{
		module_record.ProductModuleDef,
		module_homomorphism.ProductModuleOn,
		doubleConeTermsDef,
		doubleConeHorizontalDef,
		doubleConeVerticalDef,
		DoubleComplex,
		DoubleComplexMapDef,
		ConeChainComplex,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		module_homomorphism.HomZero,
		submodule.ZeroSubmodule,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
		set_basic.Extension,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀V':module_ops(A, C). " +
			"∀D':(num → num → set(C)). " +
			"∀h' v':(num → num → C → C). " +
			"∀F:(num → num → B → C).",
		Hypotheses: []string{
			"double_complex(R, V', D', h', v')",
			"double_complex_map(R, V, D, h, v, V', D', h', v', F)",
		},
		Conclusion: "double_complex(R, " +
			"    product_module(V, V'), " +
			"    double_cone_terms(V, D, D'), " +
			"    double_cone_horizontal(h, h'), " +
			"    double_cone_vertical(V, v, V', v', F))",
	}),
		"The ambient module is product_module(V, V'), V × V' componentwise (ProductModuleDef), a "+
			"module (ProductModuleOn), and each term a product of submodules ({V.zero} at q = 0, "+
			"ZeroSubmodule). The horizontal boundary is h × h', and the vertical one is each column's "+
			"cone boundary, squaring to zero as in ConeChainComplex by the vertical square of F. They "+
			"commute: on the first component by the square of D one vertical degree down (with V.zero "+
			"at q = 0), on the second by the horizontal square of F and the square of D'."),
})}

// DoubleConeTotal — the total complex of the columnwise cone of F is
// isomorphic to the cone of the total map of F, by the sign (−1)^p on the
// first component of the coordinate p.
var DoubleConeTotal = doubleConeTotalThm{family.Add(registry.ProofEntry{
	Name: "DoubleConeTotal",
	Key:  "prop_47d66df3e8b9e9dc",
	Deps: []registry.EntryLike{
		DoubleConeDoubleComplex,
		DoubleComplexMapTotal,
		DoubleTotalComplex,
		ConeChainComplex,
		ChainConeDef,
		ChainShiftDef,
		DoubleTotalDef,
		DoubleTotalTermsMember,
		DoubleTotalCoordinate,
		DoubleTotalPast,
		DoubleBoundaryCoordinate,
		DoubleBoundaryPast,
		DoubleTotalMapDef,
		doubleConeTermsDef,
		doubleConeHorizontalDef,
		doubleConeVerticalDef,
		ChainIsomorphismDef,
		module.SmulMul,
		module.SmulOne,
		module.SmulZero,
		comm_ring.AlternatingSignDef,
		comm_ring.AlternatingSignSquare,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀V':module_ops(A, C). " +
			"∀D':(num → num → set(C)). " +
			"∀h' v':(num → num → C → C). " +
			"∀F:(num → num → B → C).",
		Hypotheses: []string{
			"double_complex(R, V', D', h', v')",
			"double_complex_map(R, V, D, h, v, V', D', h', v', F)",
		},
		Conclusion: "chain_isomorphism(R, " +
			"    double_total(product_module(V, V'), " +
			"        double_cone_terms(V, D, D'), " +
			"        double_cone_horizontal(h, h'), " +
			"        double_cone_vertical(V, v, V', v', F), " +
			"        alternating_sign), " +
			"    chain_cone(«doubleTotal», " +
			"        double_total(V', D', h', v', alternating_sign), " +
			"        double_total_map(F)), " +
			"    λn:num. λu:(num → prod(B, C)). " +
			"        (λp:num. V.smul(alternating_sign(p), fst(u(p))), λp:num. snd(u(p))))",
	}),
		"A diagonal u of degree n of the cone splits into first components x_p in D(p, n − 1 − p), "+
			"x_n = V.zero, a diagonal of degree n − 1 of D, and second components y_p, a diagonal of "+
			"degree n of D'. The cone's total boundary has first component h(x_{p+1}) − "+
			"alternating_sign(p) • v(x_p), the cone of the total map −h(w_{p+1}) − alternating_sign(p) "+
			"• v(w_p); with w_p = alternating_sign(p) • x_p they agree since alternating_sign(p + 1) = "+
			"−alternating_sign(p) (AlternatingSignDef), and the second components agree with "+
			"F(alternating_sign(p) • x_p) = alternating_sign(p) • F(x_p). The map is its own inverse, "+
			"alternating_sign(p) alternating_sign(p) being R.one (AlternatingSignSquare)."),
	Reading: "The sign alternating_sign(p) is load-bearing: it flips the horizontal part, which " +
		"the cone of the total map negates with the whole total boundary and the columnwise cone " +
		"does not, its vertical boundary negating v alone. At degree 0 both sides hold (V.zero, y) " +
		"and (λp. V.zero, y'), the first component of the chain_cone being the zero diagonal.",
})}

// ColumnQuasiIsomorphismTotal — a map of double complexes that is a
// quasi-isomorphism on every column induces a quasi-isomorphism of the
// total complexes.
var ColumnQuasiIsomorphismTotal = columnQuasiIsomorphismTotalThm{family.Add(registry.ProofEntry{
	Name: "ColumnQuasiIsomorphismTotal",
	Key:  "prop_6c243d958674cec2",
	Reading: "Column p of the double cone is, term by term and boundary by " +
		"boundary, the chain_cone of the column map F(p, ·). The first quadrant, with " +
		"its finite diagonals, is what lets columnwise quasi-isomorphisms suffice.",
	Deps: []registry.EntryLike{
		DoubleColumnDef,
		DoubleColumnChainComplex,
		DoubleConeDoubleComplex,
		DoubleConeTotal,
		DoubleComplexMapTotal,
		DoubleTotalComplex,
		AcyclicAssemblyColumns,
		ConeQuasiIffAcyclic,
		ChainIsomorphismQuasiIsomorphism,
		QuasiIsomorphismAcyclic,
		ChainConeDef,
		CyclesKernel,
		BoundariesDef,
	},
	Build: family.Card(DoubleComplex.Statement(Statement{
		Binders: "∀V':module_ops(A, C). " +
			"∀D':(num → num → set(C)). " +
			"∀h' v':(num → num → C → C). " +
			"∀F:(num → num → B → C).",
		Hypotheses: []string{
			"double_complex(R, V', D', h', v')",
			"double_complex_map(R, V, D, h, v, V', D', h', v', F)",
			"∀p:num. " +
				"    quasi_isomorphism(R, " +
				"        double_column(V, D, v, p), " +
				"        double_column(V', D', v', p), " +
				"        λq:num. F(p, q))",
		},
		Conclusion: "quasi_isomorphism(R, " +
			"    «doubleTotal», " +
			"    double_total(V', D', h', v', alternating_sign), " +
			"    double_total_map(F))",
	}),
		"Column p of the cone of F is, term by term, chain_cone of the column map F(p, ·) "+
			"between the columns (DoubleColumnChainComplex), exact in every degree by "+
			"ConeQuasiIffAcyclic; read as exact_at (CyclesKernel, BoundariesDef) these are the "+
			"columns AcyclicAssemblyColumns asks for, so the total complex of the cone is exact "+
			"(DoubleConeDoubleComplex). DoubleConeTotal carries that exactness to the cone of "+
			"the total map (ChainIsomorphismQuasiIsomorphism, QuasiIsomorphismAcyclic), and "+
			"ConeQuasiIffAcyclic at the total map (DoubleComplexMapTotal) concludes."),
})}
